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

from nmigen import Const, Signal, Elaboratable, Module, Cat, Mux, Value, unsigned
from nmigen import ClockDomain, ClockSignal # , ResetSignal
from nmigen.build import Platform
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert, Past, Cover, Assume
from nmigen.cli import main_parser, main_runner
from nmigen.sim import Simulator
# from nmigen.back.pysim import Simulator #, Delay

from formal.verification import FormalData, Verification
from alu8 import ALU8Func, ALU8
from consts import AddressModes, Flags


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
    TMP16H = 8
    TMP16L = 9
    DIN = 10
    DOUT = 11


class Reg16(IntEnum):
    """Values for specifying a 16-bit register for things
    like sources and destinations."""
    NONE = 0
    PC = 1
    TMP16 = 2
    ADDR = 3


class Core(Elaboratable):
    """The core of the CPU. There is another layer wich
    handles I/O for the actual pins.
    """

    reg8_map: Dict[IntEnum, Tuple[Signal, bool]]
    reg16_map: Dict[IntEnum, Tuple[Signal, bool]]

    def __init__(self, verification: Verification = None):
        # outputs
        self.Addr = Signal(16)
        self.Dout = Signal(8)
        self.RW = Signal(reset=1)  # when 1 = read, 0 = write

        # inputs
        self.RDY = Signal()
        self.Din = Signal(8)
        self.IRQ = Signal()
        self.NMI = Signal()

        # registers
        self.a = Signal(8)
        self.x = Signal(8)
        self.y = Signal(8)
        self.sp = Signal(8, reset=0xFF)
        self.pc = Signal(16, reset_less=True)
        self.tmp8 = Signal(8)
        self.tmp16 = Signal(16)
        self.instr = Signal(8, reset_less=True)

        self.tmp16h = self.tmp16[8:]
        self.tmp16l = self.tmp16[:8]

        self.adh = self.Addr[8:]
        self.adl = self.Addr[:8]

        self.pch = self.pc[8:]
        self.pcl = self.pc[:8]

        # busses
        self.src8_1 = Signal(8)  # Input 1 of the ALU
        self.src8_2 = Signal(8)  # Input 2 of the ALU
        self.alu8 = Signal(8)   # Output from the ALU
        self.sr_flags = Signal(8)

        # selectors for busses
        self.src8_1_select = Signal(Reg8)
        self.src8_2_select = Signal(Reg8)

        # function control
        self.alu8_func = Signal(ALU8Func)

        self.reg8_map = {
            Reg8.A: (self.a, True),
            Reg8.X: (self.x, True),
            Reg8.Y: (self.y, True),
            Reg8.SP: (self.sp, True),
            Reg8.PCH: (self.pch, True),
            Reg8.PCL: (self.pcl, True),
            Reg8.TMP8: (self.tmp8, True),
            Reg8.TMP16H: (self.tmp16h, True),
            Reg8.TMP16L: (self.tmp16l, True),
            Reg8.DIN: (self.Din, False),  # read-only register
            Reg8.DOUT: (self.Dout, True),
        }
        self.reg16_map = {
            Reg16.PC: (self.pc, True),
            Reg16.TMP16: (self.tmp16, True),
            Reg16.ADDR: (self.Addr, True),
        }

        # internal state
        self.reset_state = Signal(2)  # where we are during reset
        self.cycle = Signal(4)        # where we are during instr processing

        # page boundary crossed
        self.sum9 = Signal(9)
        self.addr_ind = Signal(8)
        self.overflow = Signal()

        # mode bits
        self.mode_a = Signal(3)
        self.mode_b = Signal(3)
        self.mode_c = Signal(2)

        self.end_instr_flag = Signal()    # performs end-of-instruction actions
        self.end_instr_addr= Signal(16)  # where the next instruction is

        # Formal verification
        self.verification = verification
        self.formalData = FormalData(verification)

    def ports(self) -> List[Signal]:
        return [self.Addr, self.Din, self.Dout, self.RW, self.RDY, self.IRQ, self.NMI]

    def elaborate(self, _: Platform) -> Module:
        m = Module()

        m.submodules.alu = alu = ALU8()

        m.d.comb += self.end_instr_flag.eq(0)
        m.d.comb += self.src8_1_select.eq(Reg8.NONE)
        m.d.comb += self.src8_2_select.eq(Reg8.NONE)
        m.d.comb += self.alu8_func.eq(ALU8Func.NONE)
        m.d.ph1 += self.cycle.eq(self.cycle + 1)

        # 76543210
        # aaabbbcc
        m.d.comb += self.mode_a.eq(self.instr[5:8])
        m.d.comb += self.mode_b.eq(self.instr[2:5])
        m.d.comb += self.mode_c.eq(self.instr[0:2])

        self.src_bus_setup(m, self.reg8_map, self.src8_1, self.src8_1_select)
        self.src_bus_setup(m, self.reg8_map, self.src8_2, self.src8_2_select)

        m.d.comb += alu.input1.eq(self.src8_1)
        m.d.comb += alu.input2.eq(self.src8_2)
        m.d.comb += self.alu8.eq(alu.output)
        m.d.comb += alu.func.eq(self.alu8_func)
        m.d.comb += self.sr_flags.eq(alu.sr_flags)

        # addressing
        m.d.comb += self.addr_ind.eq(self.sum9[:8])
        m.d.comb += self.overflow.eq(self.sum9[8])

        self.reset_handler(m)
        with m.If(self.reset_state == 3):
            with m.If(self.cycle == 0):
                self.fetch(m)
            with m.Else():
                self.execute(m)
        self.maybe_do_formal_verification(m)
        self.end_instr_flag_handler(m)

        return m

    def src_bus_setup(self, m: Module, reg_map: Dict[IntEnum, Tuple[Signal, bool]], bus: Signal, selector: Signal):
        with m.Switch(selector):
            for e, reg in reg_map.items():
                with m.Case(e):
                    m.d.comb += bus.eq(reg[0])
            with m.Default():
                m.d.comb += bus.eq(0)

    def dest_bus_setup(self, m: Module, reg_map: Dict[IntEnum, Tuple[Signal, bool]], bus: Signal, bitmap: Signal):
        for e, reg in reg_map.items():
            if reg[1]:
                with m.If(bitmap[e.value]):
                    m.d.ph1 += reg[0].eq(bus)

    def read_byte(self, m: Module, cycle: int, addr: Statement,
                  comb_dest: Signal = None, sync_dest: Signal = None):
        """Reads a byte starting from the given cycle.

        The byte read is combinatorically placed in comb_dest.
        """
        with m.If(self.cycle == cycle):
            m.d.ph1 += self.Addr.eq(addr)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == cycle + 1):
            if comb_dest is not None:
                m.d.comb += comb_dest.eq(self.Din)
            if sync_dest is not None:
                m.d.ph1 += sync_dest.eq(self.Din)

    def fetch(self, m: Module):
        m.d.ph1 += self.instr.eq(self.Din)
        m.d.ph1 += self.RW.eq(1)
        m.d.ph1 += self.pc.eq(self.pc + 1)
        m.d.ph1 += self.Addr.eq(self.pc + 1)

    def end_instr(self, m: Module, addr: Statement):
        """Ends the instruction.

        Loads the PC and Addr register with the given addr, sets R/W mode
        to read, and sets the cycle to 0 at the end of the current cycle.
        """
        m.d.comb += self.end_instr_addr.eq(addr)
        m.d.comb += self.end_instr_flag.eq(1)

    def execute(self, m: Module):
        with m.Switch(self.instr):
            with m.Case(0x00):
                self.BRK(m)
            with m.Case(0x40):
                self.RTI(m)
            with m.Case(0xEA):
                self.NOP(m)
            with m.Case("00-11000"):
                self.CL_SE_C(m)
            with m.Case("11-11000"):
                self.CL_SE_D(m)
            with m.Case("01-11000"):
                self.CL_SE_I(m)
            with m.Case("10111000"):
                self.CLV(m)
            with m.Case("01-01100"):
                self.JMP(m)
            with m.Case("---10000"):
                self.BR(m)
            with m.Case(0x20):
                self.JSR(m) # JSR
            with m.Case(0x60):
                self.RTS(m)
            with m.Case(0x48):
                self.PUSH(m, register=self.a) # PHA
            with m.Case(0x08):
                self.PUSH(m, register=self.sr_flags) # PHP
            with m.Case(0x68):
                self.PULL(m, func=ALU8Func.LD, register=self.a) # PLA
            with m.Case(0x28):
                self.PULL(m, func=ALU8Func.LDSR) # PLP
            with m.Case(0xAA):
                self.TR(m, func=ALU8Func.LD, input=self.a, output=self.x) # TAX
            with m.Case(0xA8):
                self.TR(m, func=ALU8Func.LD, input=self.a, output=self.y) # TAY
            with m.Case(0xBA):
                self.TR(m, func=ALU8Func.LD, input=self.sp, output=self.x) # TSX
            with m.Case(0x8A):
                self.TR(m, func=ALU8Func.LD, input=self.x, output=self.a) # TXA
            with m.Case(0x9A):
                self.TR(m, func=ALU8Func.TR, input=self.x, output=self.sp) # TXS
            with m.Case(0x98):
                self.TR(m, func=ALU8Func.LD, input=self.y, output=self.a) # TYA
            with m.Case(0xE8):
                self.INC_DEC_IND(m, func=ALU8Func.INC, index=self.x) # INX
            with m.Case(0xC8):
                self.INC_DEC_IND(m, func=ALU8Func.INC, index=self.y) # INY
            with m.Case(0xCA):
                self.INC_DEC_IND(m, func=ALU8Func.DEC, index=self.x) # DEX
            with m.Case(0x88):
                self.INC_DEC_IND(m, func=ALU8Func.DEC, index=self.y) # DEY
            with m.Case(0x85, 0x95, 0x8D, 0x9D, 0x99, 0x81, 0x91):
                self.ST(m) # STA
            with m.Case(0x86, 0x96, 0x8E):
                self.ST(m) # STX
            with m.Case(0x84, 0x94, 0x8C):
                self.ST(m) # STY
            with m.Case(0xE6, 0xEE, 0xF6, 0xFE):
                self.ALU2(m, func=ALU8Func.INC)
            with m.Case(0xC6, 0xCE, 0xD6, 0xDE):
                self.ALU2(m, func=ALU8Func.DEC)
            with m.Case(0x0A, 0x06, 0x16, 0x0E, 0x1E):
                self.ALU2(m, func=ALU8Func.ASL)
            with m.Case(0x2A, 0x26, 0x36, 0x2E, 0x3E):
                self.ALU2(m, func=ALU8Func.ROL)
            with m.Case(0x4A, 0x46, 0x56, 0x4E, 0x5E):
                self.ALU2(m, func=ALU8Func.LSR)
            with m.Case(0x6A, 0x66, 0x76, 0x6E, 0x7E):
                self.ALU2(m, func=ALU8Func.ROR)
            with m.Case(0xE0):
                self.ALU_IMP(m, func=ALU8Func.SUB, output=self.x, store=False) # CPX imm
            with m.Case(0xE4, 0xEC):
                self.ALU(m, func=ALU8Func.SUB, x_index=self.x, output=self.x, store=False) # CPX
            with m.Case(0xC0):
                self.ALU_IMP(m, func=ALU8Func.SUB, output=self.y, store=False) # CPY imm
            with m.Case(0xC4, 0xCC):
                self.ALU(m, func=ALU8Func.SUB, x_index=self.x, output=self.y, store=False) # CPY
            with m.Case(0xA2):
                self.ALU_IMP(m, func=ALU8Func.LD, output=self.x) # LDX imm
            with m.Case(0xA0):
                self.ALU_IMP(m, func=ALU8Func.LD, output=self.y) # LDY imm
            with m.Case(0xA6, 0xB6, 0xAE, 0xBE):
                self.ALU(m, ALU8Func.LD, x_index=self.y, output=self.x) # LDX
            with m.Case(0xA4, 0xB4, 0xAC, 0xBC):
                self.ALU(m, ALU8Func.LD, x_index=self.x, output=self.y) # LDY
            with m.Case("101---01"):
                self.ALU(m, ALU8Func.LD, x_index=self.x, output=self.a)
            with m.Case("011---01"):
                self.ALU(m, ALU8Func.ADC, x_index=self.x, output=self.a)
            with m.Case("111---01"):
                self.ALU(m, ALU8Func.SBC, x_index=self.x, output=self.a)
            with m.Case("000---01"):
                self.ALU(m, ALU8Func.ORA, x_index=self.x, output=self.a)
            with m.Case("001---01"):
                self.ALU(m, ALU8Func.AND, x_index=self.x, output=self.a)
            with m.Case("010---01"):
                self.ALU(m, ALU8Func.EOR, x_index=self.x, output=self.a)
            with m.Case("0010-100"): # BIT
                self.ALU(m, ALU8Func.AND, x_index=self.x, output=self.a, store=False)
            with m.Case("110---01"): # CMP
                self.ALU(m, ALU8Func.SUB, x_index=self.x, output=self.a, store=False)
            with m.Default():  # Illegal
                self.end_instr(m, self.pc)

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
                reset_vec = Cat(self.tmp8, self.Din)
                self.end_instr(m, reset_vec)

    def end_instr_flag_handler(self, m: Module):
        with m.If(self.end_instr_flag):
            m.d.ph1 += self.pc.eq(self.end_instr_addr)
            m.d.ph1 += self.Addr.eq(self.end_instr_addr)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.cycle.eq(0)

    def interrupt_handler(self, m: Module):
        pass

    def maybe_do_formal_verification(self, m: Module):
        if self.verification is not None:
            with m.If((self.cycle == 0) & (self.reset_state == 3)):
                with m.If(self.verification.valid(self.Din)):
                    m.d.ph1 += self.formalData.preSnapshot(
                        m, self.Din, self.sr_flags, self.a, self.x, self.y, self.sp, self.pc)
                with m.Else():
                    m.d.ph1 += self.formalData.noSnapshot(m)

                with m.If(self.formalData.snapshot_taken):
                    m.d.comb += self.formalData.postSnapshot(
                        m, self.sr_flags, self.a, self.x, self.y, self.sp, self.pc)
                    self.verification.verify(m, self.instr, self.formalData)

            with m.Elif(self.formalData.snapshot_taken):
                m.d.ph1 += self.formalData.snapshot_signals(
                    m, addr=self.Addr, din=self.Din, dout=self.Dout, rw=self.RW,
                    irq=self.IRQ, nmi=self.NMI)

    def NOP(self, m: Module):
        self.end_instr(m, self.pc)

    def BRK(self, m: Module):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp)
            m.d.ph1 += self.Dout.eq((self.pc + 1)[8:]) # store PCH
            m.d.ph1 += self.RW.eq(0)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp - 1)
            m.d.ph1 += self.Dout.eq(self.pcl) # store PCL
            m.d.ph1 += self.RW.eq(0)

        with m.If(self.cycle == 3):
            m.d.ph1 += self.sp.eq(self.sp - 3)

            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp - 2)
            m.d.ph1 += self.Dout.eq(self.sr_flags | 0x30) # store SR with B = 1 (00110000)
            m.d.ph1 += self.RW.eq(0)

        with m.If(self.cycle == 4):
            m.d.ph1 += self.Addr.eq(0xFFFE)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 5):
            m.d.ph1 += self.pcl.eq(self.Din) # fetch FFFE

            m.d.ph1 += self.Addr.eq(0xFFFF)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 6):
            m.d.ph1 += self.pch.eq(self.Din) # fetch FFFF

            self.end_instr(m, Cat(self.pcl, self.Din))

    def RTI(self, m: Module):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.pc.eq(self.pc + 1)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp + 1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 3):
            # load sr flags from stack
            m.d.comb += self.src8_1.eq(0)
            m.d.comb += self.src8_2.eq(self.Din)
            m.d.comb += self.alu8_func.eq(ALU8Func.LDSR)

            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp + 2)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 4):
            m.d.ph1 += self.pcl.eq(self.Din) # fetch pcl

            m.d.ph1 += self.sp.eq(self.sp + 3)

            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp + 3)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 5):
            m.d.ph1 += self.pch.eq(self.Din) # fetch pch
            self.end_instr(m, Cat(self.pcl, self.Din))

    def JSR(self, m: Module):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.tmp16l.eq(self.Din) # fetch low address
            m.d.ph1 += self.Addr.eq(self.pc + 1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.tmp16h.eq(self.Din) # fetch high address
            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 3):
            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp)
            m.d.ph1 += self.Dout.eq(self.pch)
            m.d.ph1 += self.RW.eq(0)

            m.d.ph1 += self.sp.eq(self.sp - 1)

        with m.If(self.cycle == 4):
            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp)
            m.d.ph1 += self.Dout.eq(self.pcl)
            m.d.ph1 += self.RW.eq(0)

            m.d.ph1 += self.sp.eq(self.sp - 1)

            m.d.ph1 += self.pc.eq(self.tmp16)

        with m.If(self.cycle == 5):
            self.end_instr(m, self.pc)


    def RTS(self, m: Module):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp)
            m.d.ph1 += self.RW.eq(1)
            m.d.ph1 += self.pc.eq(self.pc + 1)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp + 1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 3):
            m.d.ph1 += self.pcl.eq(self.Din)
            m.d.ph1 += self.sp.eq(self.sp + 2)
            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp + 2)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 4):
            m.d.ph1 += self.pch.eq(self.Din)

        with m.If(self.cycle == 5):
            self.end_instr(m, self.pc)

    def PUSH(self, m: Module, register: Value):
        with m.If(self.cycle == 1):
            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp)
            m.d.ph1 += self.sp.eq(self.sp - 1)
            m.d.ph1 += self.RW.eq(0)
            m.d.ph1 += self.Dout.eq(register)

        with m.If(self.cycle == 2):
            self.end_instr(m, self.pc)

    def PULL(self, m: Module, func: ALU8Func, register: Statement = None):
        with m.If(self.cycle == 1):
            pass

        with m.If(self.cycle == 2):
            m.d.ph1 += self.adh.eq(0x01)
            m.d.ph1 += self.adl.eq(self.sp + 1)
            m.d.ph1 += self.RW.eq(1)

            m.d.ph1 += self.sp.eq(self.sp + 1)

        with m.If(self.cycle == 3):
            m.d.comb += self.src8_1.eq(0)
            m.d.comb += self.src8_2.eq(self.Din)
            m.d.comb += self.alu8_func.eq(func)

            if register is not None:
                m.d.ph1 += register.eq(self.alu8)

            self.end_instr(m, self.pc)

    def INC_DEC_IND(self, m: Module, func: ALU8Func, index: Statement):
        with m.If(self.cycle == 1):
            m.d.comb += self.src8_1.eq(index)
            m.d.comb += self.src8_2.eq(0)
            m.d.comb += self.alu8_func.eq(func)
            m.d.ph1 += index.eq(self.alu8)

            self.end_instr(m, self.pc)

    def ST(self, m: Module):
        index = Signal(8)
        zp_ind = Signal(8)

        with m.Switch(self.mode_c):
            with m.Case("01"):
                m.d.comb += index.eq(self.a)
                m.d.comb += zp_ind.eq(self.x)
            with m.Case("10"):
                m.d.comb += index.eq(self.x)
                m.d.comb += zp_ind.eq(self.y)
            with m.Case("00"):
                m.d.comb += index.eq(self.y)
                m.d.comb += zp_ind.eq(self.x)
            with m.Default():
                m.d.comb += index.eq(self.a)
                m.d.comb += zp_ind.eq(self.x)

        with m.If(self.mode_b == AddressModes.ZEROPAGE.value):
            operand = self.mode_zeropage(m)

            with m.If(self.cycle == 1):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(index)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 2):
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ZEROPAGE_IND.value):
            with m.If(self.cycle == 1):
                m.d.ph1 += self.tmp8.eq(self.Din)
                m.d.ph1 += self.pc.eq(self.pc + 1)
                m.d.ph1 += self.Addr.eq(self.Din)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.adl.eq(self.tmp8 + zp_ind)
                m.d.ph1 += self.adh.eq(0)
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Dout.eq(index)

            with m.If(self.cycle == 3):
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE.value):
            operand = self.mode_absolute(m)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(index)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 3):
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE_X.value):
            operand = self.mode_absolute(m)

            sum9 = Signal(9)

            m.d.comb += sum9.eq(self.tmp16l + self.x)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.adl.eq(sum9[:8])
                m.d.ph1 += self.adh.eq(self.Din) # high byte
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.adl.eq(sum9[:8])
                m.d.ph1 += self.adh.eq(self.tmp16h + sum9[8])
                m.d.ph1 += self.Dout.eq(self.a)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 4):
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE_Y.value):
            operand = self.mode_absolute(m)

            sum9 = Signal(9)

            m.d.comb += sum9.eq(self.tmp16l + self.y)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.adl.eq(sum9[:8])
                m.d.ph1 += self.adh.eq(self.Din) # high byte
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.adl.eq(sum9[:8])
                m.d.ph1 += self.adh.eq(self.tmp16h + sum9[8])
                m.d.ph1 += self.Dout.eq(self.a)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 4):
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.INDIRECT_X.value):
            operand, value = self.mode_indirect_x(m)

            with m.If(self.cycle == 4):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.a)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 5):
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.INDIRECT_Y.value):
            addr_ind = self.tmp16l + self.y

            with m.If(self.cycle == 1):
                m.d.ph1 += self.tmp8.eq(self.Din)
                m.d.ph1 += self.pc.eq(self.pc + 1)

                m.d.ph1 += self.adl.eq(self.Din)
                m.d.ph1 += self.adh.eq(0)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.tmp16l.eq(self.Din)
                m.d.ph1 += self.adl.eq(self.tmp8 + 1)
                m.d.ph1 += self.adh.eq(0)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.tmp16h.eq(self.Din)

                m.d.ph1 += self.adl.eq(addr_ind)
                m.d.ph1 += self.adh.eq(self.Din)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 4):
                m.d.ph1 += self.adl.eq(addr_ind)
                m.d.ph1 += self.adh.eq(self.tmp16h + addr_ind[8])
                m.d.ph1 += self.Dout.eq(self.a)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 5):
                self.end_instr(m, self.pc)

    def JMP(self, m: Module):
        # 0b01001100: 0x4C jmp $hhll
        # 0b01101100: 0x6C jmp ($hhll)

        with m.If(self.mode_a == 2):
            operand = self.mode_absolute(m)

            with m.If(self.cycle == 2):
                self.end_instr(m, operand)

        with m.Elif(self.mode_a == 3):
            operand = self.mode_indirect(m)

            with m.If(self.cycle == 4):
                self.end_instr(m, operand)

    def TR(self, m: Module, func: ALU8Func, input: Statement, output: Statement):
        with m.If(self.cycle == 1):
            m.d.comb += self.src8_1.eq(output)
            m.d.comb += self.src8_2.eq(input)
            m.d.comb += self.alu8_func.eq(func)

            m.d.ph1 += output.eq(self.alu8)

            self.end_instr(m, self.pc)

    def ALU_IMP(self, m, func: ALU8Func, output: Statement, store: bool = True):
        operand = self.mode_immediate(m)

        with m.If(self.cycle == 1):
            m.d.comb += self.src8_1.eq(output)
            m.d.comb += self.src8_2.eq(operand)
            m.d.comb += self.alu8_func.eq(func)

            if store:
                m.d.ph1 += output.eq(self.alu8)

            self.end_instr(m, self.pc + 1)

    def ALU(self, m: Module, func: ALU8Func, x_index: Statement, output: Statement, store: bool = True):
        with m.If(self.mode_b == AddressModes.INDIRECT_X.value):
            operand, value = self.mode_indirect_x(m)

            with m.If(self.cycle == 5):
                m.d.comb += self.src8_1.eq(output)
                m.d.comb += self.src8_2.eq(value)
                m.d.comb += self.alu8_func.eq(func)

                if store:
                    m.d.ph1 += output.eq(self.alu8)

                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ZEROPAGE.value):
            operand = self.mode_zeropage(m)

            self.read_byte(m, cycle=1, addr=operand, comb_dest=self.src8_2)

            with m.If(self.cycle == 2):
                m.d.comb += self.src8_1.eq(output)
                m.d.comb += self.alu8_func.eq(func)

                if store:
                    m.d.ph1 += output.eq(self.alu8)

                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.IMMEDIATE.value):
            operand = self.mode_immediate(m)

            with m.If(self.cycle == 1):
                m.d.comb += self.src8_1.eq(output)
                m.d.comb += self.src8_2.eq(operand)
                m.d.comb += self.alu8_func.eq(func)

                if store:
                    m.d.ph1 += output.eq(self.alu8)

                self.end_instr(m, self.pc + 1)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE.value):
            operand = self.mode_absolute(m)

            self.read_byte(m, cycle=2, addr=operand, comb_dest=self.src8_2)

            with m.If(self.cycle == 3):
                m.d.comb += self.src8_1.eq(output)
                m.d.comb += self.alu8_func.eq(func)

                if store:
                    m.d.ph1 += output.eq(self.alu8)

                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.INDIRECT_Y.value):
            operand = self.mode_indirect_y(m)

            with m.If(self.cycle == 4):
                m.d.comb += self.src8_1.eq(output)
                m.d.comb += self.src8_2.eq(operand)
                m.d.comb += self.alu8_func.eq(func)

                if store:
                    m.d.ph1 += output.eq(self.alu8)

            with m.If(self.cycle == 5):
                m.d.comb += self.src8_1.eq(output)
                m.d.comb += self.src8_2.eq(operand)
                m.d.comb += self.alu8_func.eq(func)

                if store:
                    m.d.ph1 += output.eq(self.alu8)

        with m.Elif(self.mode_b == AddressModes.ZEROPAGE_IND.value):
            with m.If(self.cycle == 1):
                m.d.ph1 += self.pc.eq(self.pc + 1)

                m.d.ph1 += self.tmp8.eq(self.Din) # zp
                m.d.ph1 += self.adl.eq(self.Din)
                m.d.ph1 += self.adh.eq(0)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.adl.eq(self.tmp8 + x_index) # zp + X
                m.d.ph1 += self.adh.eq(0)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                m.d.comb += self.src8_1.eq(output)
                m.d.comb += self.src8_2.eq(self.Din)
                m.d.comb += self.alu8_func.eq(func)

                if store:
                    m.d.ph1 += output.eq(self.alu8)

                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE_Y.value):
            self.mode_absolute_indexed(m, func=func, index=self.y, output=output, store=store)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE_X.value):
            self.mode_absolute_indexed(m, func=func, index=x_index, output=output, store=store)

    def BR(self, m: Module):
        """Branch instructions."""

        operand = self.mode_immediate(m)

        sum9 = Signal(9)
        m.d.comb += sum9.eq(self.pcl + operand)

        backwards = operand[7]
        co = sum9[8]

        crossed = Signal()
        m.d.comb += crossed.eq(co ^ backwards)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.tmp16l.eq(sum9[:8])
            m.d.ph1 += self.tmp16h.eq(self.pch)

        with m.If(self.cycle == 3):
            take_branch = self.branch_cond(m)

            with m.If(take_branch):
                with m.If(crossed):
                    m.d.ph1 += self.tmp16h.eq(Mux(backwards,
                                                  self.tmp16h - crossed,
                                                  self.tmp16h + crossed))
                with m.Else():
                    self.end_instr(m, self.tmp16)

            with m.Else():
                self.end_instr(m, self.pc)

        with m.If(self.cycle == 4):
            self.end_instr(m, self.tmp16)

    def branch_cond(self, m: Module) -> Signal:
        cond = Signal()

        with m.Switch(self.mode_a):
            with m.Case(0): # BPL
                m.d.comb += cond.eq(~self.sr_flags[Flags.N])
            with m.Case(1): # BMI
                m.d.comb += cond.eq(self.sr_flags[Flags.N])
            with m.Case(2): # BVC
                m.d.comb += cond.eq(~self.sr_flags[Flags.V])
            with m.Case(3): # BVS
                m.d.comb += cond.eq(self.sr_flags[Flags.V])
            with m.Case(4): # BCC
                m.d.comb += cond.eq(~self.sr_flags[Flags.C])
            with m.Case(5): # BCS
                m.d.comb += cond.eq(self.sr_flags[Flags.C])
            with m.Case(6): # BNE
                m.d.comb += cond.eq(~self.sr_flags[Flags.Z])
            with m.Case(7): # BEQ
                m.d.comb += cond.eq(self.sr_flags[Flags.Z])

        return cond

    def CL_SE_C(self, m: Module):
        """Clears or sets carry flag."""
        with m.If(self.cycle == 1):
            m.d.comb += self.alu8_func.eq(
                Mux(self.instr[5], ALU8Func.SEC, ALU8Func.CLC))
            self.end_instr(m, self.pc)

    def CL_SE_D(self, m: Module):
        """Clears or sets decimal flag."""
        with m.If(self.cycle == 1):
            m.d.comb += self.alu8_func.eq(
                Mux(self.instr[5], ALU8Func.SED, ALU8Func.CLD))
            self.end_instr(m, self.pc)

    def CL_SE_I(self, m: Module):
        """Clears or sets interrupt flag."""
        with m.If(self.cycle == 1):
            m.d.comb += self.alu8_func.eq(
                Mux(self.instr[5], ALU8Func.SEI, ALU8Func.CLI))
            self.end_instr(m, self.pc)

    def CLV(self, m: Module):
        """Clears overflow flag."""
        with m.If(self.cycle == 1):
            m.d.comb += self.alu8_func.eq(ALU8Func.CLV)
            self.end_instr(m, self.pc)

    def ALU2(self, m: Module, func: ALU8Func):
        # implied accumulator mode
        with m.If(self.mode_b == AddressModes.IMMEDIATE.value):
            with m.If(self.cycle == 1):
                m.d.comb += self.src8_1.eq(self.a)
                m.d.comb += self.src8_2.eq(0)
                m.d.comb += self.alu8_func.eq(func)
                m.d.ph1 += self.a.eq(self.alu8)

                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ZEROPAGE.value):
            operand = self.mode_zeropage(m)

            self.read_byte(m, cycle=1, addr=operand, comb_dest=self.src8_1)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.tmp8.eq(self.src8_1)
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.src8_1)

            with m.If(self.cycle == 3):
                m.d.comb += self.src8_1.eq(self.tmp8)
                m.d.comb += self.src8_2.eq(0)
                m.d.comb += self.alu8_func.eq(func)

                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.alu8)

            with m.If(self.cycle == 4):
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ZEROPAGE_IND.value):
            zp_ind = (self.tmp16l + self.x)[:8]

            with m.If(self.cycle == 1):
                m.d.ph1 += self.tmp16l.eq(self.Din)
                m.d.ph1 += self.tmp16h.eq(0)
                m.d.ph1 += self.adl.eq(self.Din)
                m.d.ph1 += self.adh.eq(0)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.tmp16l.eq(zp_ind)
                m.d.ph1 += self.adl.eq(zp_ind)
                m.d.ph1 += self.adh.eq(0)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.tmp8.eq(self.Din)
                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Addr.eq(self.tmp16)

            with m.If(self.cycle == 4):
                m.d.comb += self.src8_1.eq(self.tmp8)
                m.d.comb += self.src8_2.eq(0)
                m.d.comb += self.alu8_func.eq(func)

                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.alu8)

            with m.If(self.cycle == 5):
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE.value):
            operand = self.mode_absolute(m)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.tmp8.eq(self.Din)

                m.d.ph1 += self.RW.eq(1)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.Din)

            with m.If(self.cycle == 4):
                m.d.comb += self.src8_1.eq(self.tmp8)
                m.d.comb += self.src8_2.eq(0)
                m.d.comb += self.alu8_func.eq(func)

                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.alu8)

            with m.If(self.cycle == 5):
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE_X.value):
            sum9 = Signal(9)
            overflow = Signal()
            m.d.comb += sum9.eq(self.tmp16l + self.x)
            m.d.comb += overflow.eq(sum9[8])

            with m.If(self.cycle == 1):
                m.d.ph1 += self.tmp16l.eq(self.Din)
                m.d.ph1 += self.pc.eq(self.pc + 1)
                m.d.ph1 += self.Addr.eq(self.pc + 1)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.pc.eq(self.pc + 1)
                m.d.ph1 += self.tmp16l.eq(sum9[:8])
                m.d.ph1 += self.tmp16h.eq(self.Din + overflow)
                m.d.ph1 += self.Addr.eq(Cat(sum9[:8], self.tmp16h))
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                # re-read from corrected address
                m.d.ph1 += self.Addr.eq(self.tmp16)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 4):
                m.d.ph1 += self.tmp8.eq(self.Din)

                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.Din)

            with m.If(self.cycle == 5):
                m.d.comb += self.src8_1.eq(self.tmp8)
                m.d.comb += self.src8_2.eq(0)
                m.d.comb += self.alu8_func.eq(func)

                m.d.ph1 += self.RW.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.alu8)

            with m.If(self.cycle == 6):
                self.end_instr(m, self.pc)

    def mode_indirect_x(self, m: Module) -> List[Statement]:
        """Generates logic to get 8-bit operand for indexed indirect addressing instructions.
        """
        value = Mux(self.cycle == 4, self.Din, self.tmp8)
        operand = self.tmp16

        addr_ind = self.Din + self.x

        with m.If(self.cycle == 1):
            # fetch pointer
            m.d.ph1 += self.tmp8.eq(addr_ind)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.adh.eq(0)
            m.d.ph1 += self.adl.eq(addr_ind)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 2):
            # read low byte
            m.d.ph1 += self.tmp16l.eq(self.Din)
            m.d.ph1 += self.adh.eq(0)
            m.d.ph1 += self.adl.eq(self.tmp8 + 1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 3):
            # read high byte
            m.d.ph1 += self.tmp16h.eq(self.Din)
            m.d.ph1 += self.adh.eq(self.Din)
            m.d.ph1 += self.adl.eq(self.tmp16l)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 4):
            # read value
            m.d.ph1 += self.tmp8.eq(self.Din)

        return [operand, value]

    def mode_immediate(self, m: Module) -> Statement:
        """Generates logic to get the 8-bit operand for immediate mode instructions.

        Returns a Statement containing an 8-bit operand.
        After cycle 1, tmp8 contains the operand.
        """
        operand = Mux(self.cycle == 1, self.Din, self.tmp8)

        with m.If(self.cycle == 1):
            m.d.ph1 += self.tmp8.eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.Addr.eq(self.pc + 1)
            m.d.ph1 += self.RW.eq(1)

        return operand

    def mode_zeropage(self, m: Module) -> Statement:
        """Generates logic to get the 8-bit zero-page address for zeropage mode instructions.

        Returns a Statement containing a 16-bit address where the upper byte is zero.
        After cycle 1, tmp16 contains the address.
        """
        operand = Mux(self.cycle == 1, self.Din, self.tmp16)

        with m.If(self.cycle == 1):
            m.d.ph1 += self.tmp16h.eq(0)
            m.d.ph1 += self.tmp16l.eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.Addr.eq(self.pc + 1)
            m.d.ph1 += self.RW.eq(1)

        return operand

    def mode_zeropage_indexed(self, m: Module, index: Signal) -> Statement:
        """Generates logic to get the 8-bit zero-page address for zeropage X mode instructions.

        Returns a Statement containing a 16-bit address where the upper byte is zero.
        After cycle 1, tmp16 contains the address.
        """
        operand = Mux(self.cycle == 1, self.Din, self.tmp16)

        with m.If(self.cycle == 1):
            m.d.ph1 += self.tmp16l.eq(self.Din + index)
            m.d.ph1 += self.tmp16h.eq(0)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.Addr.eq(self.pc + 1)
            m.d.ph1 += self.RW.eq(1)

        return operand

    def mode_absolute(self, m: Module) -> Statement:
        """Generates logic to get the 16-bit operand for extended mode instructions.

        Returns a Statement containing the 16-bit operand. After cycle 2, tmp16
        contains the operand.
        """
        operand = Mux(self.cycle == 2, Cat(self.tmp16l, self.Din), self.tmp16)

        with m.If(self.cycle == 1):
            m.d.ph1 += self.tmp16l.eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.Addr.eq(self.pc + 1)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.tmp16h.eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)

        return operand

    def mode_indirect_y(self, m: Module, write: bool = False) -> Statement:
        sum9  = Signal(9)
        overflow = Signal()

        m.d.comb += sum9.eq(self.tmp16l + self.y)
        m.d.comb += overflow.eq(sum9[8])

        operand = self.Din

        # fetch pointer address
        with m.If(self.cycle == 1):
            m.d.ph1 += self.tmp8.eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.adl.eq(self.Din)
            m.d.ph1 += self.adh.eq(0)
            m.d.ph1 += self.RW.eq(1)

        # fetch address low
        with m.If(self.cycle == 2):
            m.d.ph1 += self.tmp16l.eq(self.Din)
            m.d.ph1 += self.adl.eq(self.tmp8 + 1)
            m.d.ph1 += self.adh.eq(0)
            m.d.ph1 += self.RW.eq(1)

        # fetch address high
        with m.If(self.cycle == 3):
            m.d.ph1 += self.tmp16h.eq(self.Din)

            # read from effective address (maybe incorrect)
            m.d.ph1 += self.adl.eq(sum9[:8])
            m.d.ph1 += self.adh.eq(self.Din)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 4):
            # prepare to read from corrected effective address
            with m.If(overflow):
                m.d.ph1 += self.adl.eq(self.tmp16l)
                m.d.ph1 += self.adh.eq(self.tmp16h + overflow)
                m.d.ph1 += self.RW.eq(1)

            with m.Else():
                self.end_instr(m, self.pc)

        return operand

    def mode_absolute_indexed(self, m: Module, func: ALU8Func, index: Signal, output: Statement, store: bool = True):
        m.d.comb += self.sum9.eq(self.tmp16l + index)

        # fetch low operand
        with m.If(self.cycle == 1):
            m.d.ph1 += self.tmp16l.eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.Addr.eq(self.pc + 1)
            m.d.ph1 += self.RW.eq(1)

        # fetch high operand
        with m.If(self.cycle == 2):
            m.d.ph1 += self.tmp16h.eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            # read from address + I
            m.d.ph1 += self.Addr.eq(Cat(self.addr_ind, self.Din))
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 3):
            with m.If(self.overflow):
                # fix the high byte if overflowed
                m.d.ph1 += self.tmp16h.eq(self.tmp16h + 1)
                m.d.ph1 += self.adl.eq(self.addr_ind)
                m.d.ph1 += self.adh.eq(self.tmp16h + 1)
                m.d.ph1 += self.RW.eq(1)

            with m.Else():
                # assign readed value
                m.d.comb += self.src8_1.eq(output)
                m.d.comb += self.src8_2.eq(self.Din)
                m.d.comb += self.alu8_func.eq(func)

                if store:
                    m.d.ph1 += output.eq(self.alu8)

                self.end_instr(m, self.pc)

        with m.If(self.cycle == 4):
            # execute only if page boundary crossed
            m.d.comb += self.src8_1.eq(output)
            m.d.comb += self.src8_2.eq(self.Din)
            m.d.comb += self.alu8_func.eq(func)

            if store:
                m.d.ph1 += output.eq(self.alu8)

            self.end_instr(m, self.pc)

    def mode_indirect(self, m: Module) -> Statement:
        """Generates logic to get the 16-bit address for indirect mode instructions.

        Returns a Statement containing the 16-bit address. After cycle 4, tmp16
        contains the address.
        """

        pointer = self.mode_absolute(m)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.Addr.eq(pointer)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 3):
            m.d.ph1 += self.pcl.eq(self.Din)

            m.d.ph1 += self.adl.eq(pointer[:8] + 1)
            m.d.ph1 += self.adh.eq(pointer[8:])
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == 4):
            m.d.ph1 += self.pch.eq(self.Din)

        operand = Mux(self.cycle == 4, Cat(self.pcl, self.Din), self.pc)

        return operand

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
            m.d.ph1 += Cover(core.formalData.snapshot_taken &
                             core.end_instr_flag)
            m.d.ph1 += Assume(core.formalData.snapshot_taken &
                              core.end_instr_flag)

        # Verify reset does what it's supposed to
        with m.If(Past(rst, 4) & ~Past(rst, 3) & ~Past(rst, 2) & ~Past(rst)):
            m.d.ph1 += Assert(Past(core.Addr, 2) == 0xFFFE)
            m.d.ph1 += Assert(Past(core.Addr) == 0xFFFF)
            m.d.ph1 += Assert(core.Addr[:8] == Past(core.Din, 2))
            m.d.ph1 += Assert(core.Addr[8:] == Past(core.Din))
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
            for _ in range(20):
                yield

        sim.add_sync_process(process, domain="ph1")
        with sim.write_vcd("test.vcd", "test.gtkw", traces=core.ports()):
            sim.run()
