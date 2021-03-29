# Core of 6502 CPU

# Copyright (C) 2021 M.Magomedov <mmagomedoff@gmail.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

from enum import IntEnum
from typing import List, Dict, Tuple, Optional
import importlib

from nmigen import Signal, Value, Elaboratable, Module, Cat, Const, Mux
from nmigen import ClockDomain, ClockSignal # , ResetSignal
from nmigen.build import Platform
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert, Past, Cover, Assume
from nmigen.cli import main_parser, main_runner
from nmigen.back.pysim import Simulator #, Delay

from formal.verification import FormalData, Verification

class Reg8(IntEnum):
    """Values for specifying an 8-bit register for things
    like sources and destinations. Can also specify the
    (H)igh or (L)ow 8 bits of a 16-bit signal."""
    NONE = 0
    A = 1
    X = 2
    Y = 3
    PCH = 4
    PCL = 5
    SP = 6
    TMP8 = 7
    DIN = 8
    DOUT = 9


class Reg16(IntEnum):
    """Values for specifying a 16-bit register for things
    like sources and destinations."""
    NONE = 0
    PC = 1
    ADDR = 2


class Core(Elaboratable):
    """The core of the CPU. There is another layer wich
    handles I/O for the actual pins.
    """

    reg8_map: Dict[IntEnum, Tuple[Signal, bool]]
    reg16_map: Dict[IntEnum, Tuple[Signal, bool]]

    def __init__(self, verification: Verification = None):
        self.Addr = Signal(16)
        self.Din = Signal(8)
        self.Dout = Signal(8)
        self.RW = Signal(reset=1)  # 1 = read, 0 = write

        self.a = Signal(8)
        self.x = Signal(8)
        self.y = Signal(8)

        self.sp = Signal(8, reset_less=True)
        self.pc = Signal(16, reset_less=True)

        self.tmp8 = Signal(8)
        self.tmp16 = Signal(16)

        self.instr = Signal(8, reset_less=True)

        self.reg8_map = {
            Reg8.A: (self.a, True),
            Reg8.X: (self.x, True),
            Reg8.Y: (self.y, True),
            Reg8.SP: (self.sp, True),
            Reg8.PCH: (self.pc[8:], True),
            Reg8.PCL: (self.pc[:8], True),
            Reg8.DIN: (self.Din, False),  # read-only register
            Reg8.DOUT: (self.Dout, True),
        }
        self.reg16_map = {
            Reg16.PC: (self.pc, True),
            Reg16.ADDR: (self.Addr, True),
        }

        self.reset_state = Signal(2)  # where we are during reset
        self.cycle = Signal(4)        # where we are during instr processing

        self.end_instr_flag = Signal()    # performs end-of-instruction actions
        self.end_instr_addr = Signal(16)  # where the next instruction is

        # Formal verification
        self.verification = verification
        self.formal_data = FormalData(verification)

    def ports(self) -> List[Signal]:
        return [self.Addr, self.Din, self.Dout, self.RW]

    def elaborate(self, _: Platform) -> Module:
        m = Module()

        m.d.comb += self.end_instr_flag.eq(0)

        self.reset_handler(m)
        self.end_instr_flag_handler(m)

        with m.If(self.reset_state == 3):
            with m.If(self.cycle == 0):
                self.fetch(m)
            with m.Else():
                self.execute(m)
        self.maybe_do_formal_verification(m)

        return m

    def fetch(self, m: Module):
        m.d.ph1 += self.instr.eq(self.Din)
        m.d.ph1 += self.cycle.eq(1)
        m.d.ph1 += self.RW.eq(1)
        m.d.ph1 += self.pc.eq(self.pc + 1)
        m.d.ph1 += self.Addr.eq(self.pc + 1)

    def execute(self, m: Module):
        with m.Switch(self.instr):
            with m.Case(0xEA):
                self.NOP(m)
            with m.Case(0x4C):
                self.JMPAbs(m)
            with m.Default():  # Illegal
                self.end_instr(m, self.pc)

    def NOP(self, m: Module):
        self.end_instr(m, self.pc)

    def JMPAbs(self, m: Module):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.tmp16[8:].eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.Addr.eq(self.pc + 1)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.cycle.eq(2)
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

        with m.If(self.cycle == 2):
            new_pc = Cat(self.Din, self.tmp16[8:])
            self.end_instr(m, new_pc)
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

    def end_instr(self, m: Module, addr: Statement):
        m.d.comb += self.end_instr_addr.eq(addr)
        m.d.comb += self.end_instr_flag.eq(1)

    def reset_handler(self, m: Module):
        with m.Switch(self.reset_state):
            with m.Case(0):
                m.d.ph1 += self.Addr.eq(0xFFFE)
                m.d.ph1 += self.RW.eq(1)
                m.d.ph1 += self.reset_state.eq(1)
            with m.Case(1):
                m.d.ph1 += self.Addr.eq(0xFFFF)
                m.d.ph1 += self.RW.eq(1)
                m.d.ph1 += self.tmp8.eq(self.Din)
                m.d.ph1 += self.reset_state.eq(2)
            with m.Case(2):
                m.d.ph1 += self.reset_state.eq(3)
                reset_vec = Cat(self.Din, self.tmp8)
                self.end_instr(m, reset_vec)

    def end_instr_flag_handler(self, m: Module):
        with m.If(self.end_instr_flag):
            m.d.ph1 += self.pc.eq(self.end_instr_addr)
            m.d.ph1 += self.Addr.eq(self.end_instr_addr)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.cycle.eq(0)

    def maybe_do_formal_verification(self, m: Module):
        if self.verification is not None:
            with m.If((self.cycle == 0) & (self.reset_state == 3)):
                with m.If(self.verification.valid(self.Din)):
                    self.formal_data.preSnapshot(
                        m, self.Din, self.a, self.x, self.y, self.sp, self.pc)
                with m.Else():
                    self.formal_data.noSnapshot(m)

                with m.If(self.formal_data.snapshot_taken):
                    self.formal_data.postSnapshot(
                        m, self.a, self.x, self.y, self.sp, self.pc)
                    self.verification.check(m, self.instr, self.formal_data)

if __name__ == "__main__":
    parser = main_parser()
    parser.add_argument("--insn")
    args = parser.parse_args()

    verification: Optional[Verification] = None
    if args.insn is not None:
        module = importlib.import_module(f"formal.formal_{args.insn}")
        formal_class = getattr(module, "Formal")
        verification = formal_class()

    m = Module()
    m.submodules.core = core = Core(verification)
    m.domains.ph1 = ph1 = ClockDomain("ph1")

    rst = Signal()
    ph1clk = ClockSignal("ph1")
    ph1.rst = rst

    if verification is not None:
        # Cycle counter
        cycle2 = Signal(6, reset_less=True)
        m.d.ph1 += cycle2.eq(cycle2 + 1)

        # Force a reset
        # m.d.comb += Assume(rst == (cycle2 < 8))

        with m.If(cycle2 == 20):
            m.d.ph1 += Cover(verification.valid(core.instr))
            m.d.ph1 += Assume(verification.valid(core.instr))

        # Verify reset does what it's supposed to
        with m.If(Past(rst, 4) & ~Past(rst, 3) & ~Past(rst, 2) & ~Past(rst)):
            m.d.ph1 += Assert(Past(core.Addr, 2) == 0xFFFE)
            m.d.ph1 += Assert(Past(core.Addr) == 0xFFFF)
            m.d.ph1 += Assert(core.Addr[8:] == Past(core.Din, 2))
            m.d.ph1 += Assert(core.Addr[:8] == Past(core.Din))
            m.d.ph1 += Assert(core.Addr == core.pc)

        main_runner(parser, args, m, ports=core.ports() + [ph1clk, rst])

    else:
        # Fake memory
        mem = {
            0xFFFE: 0x12,
            0xFFFF: 0x34,
            0x1234: 0x4C,  # JMP 0xA010
            0x1235: 0xA0,
            0x1236: 0x10,
            0xA010: 0xEA,  # NOP
        }
        with m.Switch(core.Addr):
            for addr, data in mem.items():
                with m.Case(addr):
                    m.d.comb += core.Din.eq(data)
            with m.Default():
                m.d.comb += core.Din.eq(0xFF)

        sim = Simulator(m)
        sim.add_clock(1e-6, domain="ph1")

        def process():
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield
            yield

        sim.add_sync_process(process, domain="ph1")
        with sim.write_vcd("test.vcd", "test.gtkw", traces=core.ports()):
            sim.run()
