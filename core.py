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

from nmigen import Const, Signal, Elaboratable, Module, Cat, Mux
from nmigen import ClockDomain, ClockSignal # , ResetSignal
from nmigen.build import Platform
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert, Past, Cover, Assume
from nmigen.cli import main_parser, main_runner
from nmigen.back.pysim import Simulator #, Delay

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
        self.Addr = Signal(16)
        self.Din = Signal(8)
        self.Dout = Signal(8)
        self.RW = Signal(reset=1)  # when 1 = read, 0 = write
        self.VMA = Signal()  # when 1 = address is valid

        self.a = Signal(8)
        self.x = Signal(8)
        self.y = Signal(8)

        self.sp = Signal(8, reset_less=True)
        self.pc = Signal(16, reset_less=True)

        self.tmp8 = Signal(8)
        self.tmp16 = Signal(16)

        self.instr = Signal(8, reset_less=True)

        self.tmp16h = self.tmp16[8:]
        self.tmp16l = self.tmp16[:8]

        self.adh = self.Addr[8:]
        self.adl = self.Addr[:8]

        self.pcl = self.pc[:8]
        self.pch = self.pc[8:]

        # busses
        self.src8_1 = Signal(8)  # Input 1 of the ALU
        self.src8_2 = Signal(8)  # Input 2 of the ALU
        self.alu8 = Signal(8)   # Output from the ALU

        # selectors for busses
        self.src8_1_select = Signal(Reg8)
        self.src8_2_select = Signal(Reg8)

        # function control
        self.alu8_func = Signal(ALU8Func)

        self.sr_flags = Signal(8)

        self.reg8_map = {
            Reg8.A: (self.a, True),
            Reg8.X: (self.x, True),
            Reg8.Y: (self.y, True),
            Reg8.SP: (self.sp, True),
            Reg8.PCH: (self.pc[:8], True),
            Reg8.PCL: (self.pc[8:], True),
            Reg8.TMP16H: (self.tmp16[:8], True),
            Reg8.TMP16L: (self.tmp16[8:], True),
            Reg8.DIN: (self.Din, False),  # read-only register
            Reg8.DOUT: (self.Dout, True),
        }
        self.reg16_map = {
            Reg16.PC: (self.pc, True),
            Reg16.TMP16: (self.tmp16, True),
            Reg16.ADDR: (self.Addr, True),
        }

        self.reset_state = Signal(2)  # where we are during reset
        self.cycle = Signal(4)        # where we are during instr processing

        # mode bits
        self.mode_a = Signal(3)
        self.mode_b = Signal(3)
        self.mode_c = Signal(2)

        self.end_instr_flag = Signal()    # performs end-of-instruction actions
        self.end_instr_addr= Signal(16)  # where the next instruction is

        # Formal verification
        self.verification = verification
        self.formal_data = FormalData(verification)

    def ports(self) -> List[Signal]:
        return [self.Addr, self.Din, self.Dout, self.RW]

    def elaborate(self, _: Platform) -> Module:
        m = Module()

        m.submodules.alu = alu = ALU8()

        m.d.comb += self.end_instr_flag.eq(0)
        m.d.comb += self.src8_1_select.eq(Reg8.NONE)
        m.d.comb += self.src8_2_select.eq(Reg8.NONE)
        m.d.comb += self.alu8_func.eq(ALU8Func.NONE)
        m.d.ph1 += self.VMA.eq(1)
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

    def read_byte(self, m: Module, cycle: int, addr: Statement, comb_dest: Signal):
        """Reads a byte starting from the given cycle.

        The byte read is combinatorically placed in comb_dest.
        """
        with m.If(self.cycle == cycle):
            m.d.ph1 += self.Addr.eq(addr)
            m.d.ph1 += self.RW.eq(1)

        with m.If(self.cycle == cycle + 1):
            m.d.comb += comb_dest.eq(self.Din)
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

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
            with m.Case(0xEA):
                self.NOP(m)
            with m.Case("01-01100"):
                self.JMP(m)
            with m.Case("---10000"):
                self.BR(m)
            with m.Case("100---01"):
                self.STA(m)
            with m.Case(0x86, 0x96, 0x8E):
                self.STX(m)
            with m.Case(0x84, 0x94, 0x8C):
                self.STY(m)
            with m.Case("101---01"):
                self.ALU(m, ALU8Func.LD)
            with m.Case("011---01"):
                self.ALU(m, ALU8Func.ADC)
            with m.Case("111---01"):
                self.ALU(m, ALU8Func.SBC)
            with m.Case("000---01"):
                self.ALU(m, ALU8Func.ORA)
            with m.Case("001---01"):
                self.ALU(m, ALU8Func.AND)
            with m.Case("010---01"):
                self.ALU(m, ALU8Func.EOR)
            with m.Case("0010-100"): # BIT
                self.ALU(m, ALU8Func.AND, store=False)
            with m.Case("110---01"): # CMP
                self.ALU(m, ALU8Func.SUB, store=False)
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

    def maybe_do_formal_verification(self, m: Module):
        if self.verification is not None:
            with m.If((self.cycle == 0) & (self.reset_state == 3)):
                with m.If(self.verification.valid(self.Din)):
                    self.formal_data.preSnapshot(
                        m, self.Din, self.sr_flags, self.a, self.x, self.y, self.sp, self.pc)
                with m.Else():
                    self.formal_data.noSnapshot(m)

                with m.If(self.formal_data.snapshot_taken):
                    self.formal_data.postSnapshot(
                        m, self.sr_flags, self.a, self.x, self.y, self.sp, self.pc)
                    self.verification.check(m, self.instr, self.formal_data)

    def NOP(self, m: Module):
        self.end_instr(m, self.pc)

    def STX(self, m: Module):
        with m.If(self.mode_b == AddressModes.ZEROPAGE.value):
            operand = self.mode_zeropage(m)

            with m.If(self.cycle == 1):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.x)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 3):
                if self.verification is not None:
                    self.formal_data.write(m, self.Addr, self.Dout)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ZEROPAGE_IND.value):
            operand = self.mode_zeropage_indexed(m, index=self.y)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.y)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 4):
                if self.verification is not None:
                    self.formal_data.write(m, self.Addr, self.Dout)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE.value):
            operand = self.mode_absolute(m)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.x)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 4):
                if self.verification is not None:
                    self.formal_data.write(m, self.Addr, self.Dout)
                self.end_instr(m, self.pc)

    def STY(self, m: Module):
        with m.If(self.mode_b == AddressModes.ZEROPAGE.value):
            operand = self.mode_zeropage(m)

            with m.If(self.cycle == 1):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.y)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 3):
                if self.verification is not None:
                    self.formal_data.write(m, self.Addr, self.Dout)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ZEROPAGE_IND.value):
            operand = self.mode_zeropage_indexed(m, index=self.x)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.y)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 4):
                if self.verification is not None:
                    self.formal_data.write(m, self.Addr, self.Dout)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE.value):
            operand = self.mode_absolute(m)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.y)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 4):
                if self.verification is not None:
                    self.formal_data.write(m, self.Addr, self.Dout)
                self.end_instr(m, self.pc)

    def STA(self, m: Module):
        with m.If(self.mode_b == AddressModes.ZEROPAGE.value):
            operand = self.mode_zeropage(m)

            with m.If(self.cycle == 1):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.a)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 3):
                if self.verification is not None:
                    self.formal_data.write(m, self.Addr, self.Dout)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ZEROPAGE_IND.value):
            operand = self.mode_zeropage_indexed(m, index=self.x)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.a)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 4):
                if self.verification is not None:
                    self.formal_data.write(m, self.Addr, self.Dout)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE.value):
            operand = self.mode_absolute(m)

            with m.If(self.cycle == 2):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 3):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.a)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 4):
                if self.verification is not None:
                    self.formal_data.write(m, self.Addr, self.Dout)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE_X.value):
            operand = self.mode_absolute(m)

            sum9 = self.tmp16l + self.x

            with m.If(self.cycle == 2):
                m.d.ph1 += self.tmp16l.eq(sum9[:8])

            with m.If(self.cycle == 3):
                m.d.ph1 += self.tmp16h.eq(self.tmp16h + sum9[8])
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 4):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.a)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 5):
                if self.verification is not None:
                    self.formal_data.write(m, self.Addr, self.Dout)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE_Y.value):
            operand = self.mode_absolute(m)

            sum9 = self.tmp16l + self.y

            with m.If(self.cycle == 2):
                m.d.ph1 += self.tmp16l.eq(sum9[:8])

            with m.If(self.cycle == 3):
                m.d.ph1 += self.tmp16h.eq(self.tmp16h + sum9[8])
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 4):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.a)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 5):
                if self.verification is not None:
                    self.formal_data.write(m, self.Addr, self.Dout)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.INDIRECT_X.value):
            operand = self.mode_indirect_x(m)

            with m.If(self.cycle == 4):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.adl.eq(operand)
                m.d.ph1 += self.adh.eq(0)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 5):
                m.d.ph1 += self.adl.eq(operand)
                m.d.ph1 += self.adh.eq(0)
                m.d.ph1 += self.Dout.eq(self.a)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 6):
                if self.verification is not None:
                    self.formal_data.write(m, self.Addr, self.Dout)
                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.INDIRECT_Y.value):
            operand = self.mode_indirect_y(m, write=True)

            with m.If(self.cycle == 4):
                m.d.ph1 += self.VMA.eq(0)
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

            with m.If(self.cycle == 5):
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.Dout.eq(self.a)
                m.d.ph1 += self.RW.eq(0)

            with m.If(self.cycle == 6):
                if self.verification is not None:
                    self.formal_data.write(m, self.Addr, self.Dout)
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

    def ALU(self, m: Module, func: ALU8Func, store: bool = True):
        with m.If(self.mode_b == AddressModes.INDIRECT_X.value):
            value = self.mode_indirect_x(m)

            with m.If(self.cycle == 5):
                m.d.comb += self.src8_1.eq(self.a)
                m.d.comb += self.src8_2.eq(value)
                m.d.comb += self.alu8_func.eq(func)

                if store:
                    m.d.ph1 += self.a.eq(self.alu8)

                self.end_instr(m, self.pc)

        with m.If(self.mode_b == AddressModes.ZEROPAGE.value):
            operand = self.mode_zeropage(m)

            self.read_byte(m, cycle=1, addr=operand, comb_dest=self.src8_2)

            with m.If(self.cycle == 2):
                m.d.comb += self.src8_1.eq(self.a)
                m.d.comb += self.alu8_func.eq(func)

                if store:
                    m.d.ph1 += self.a.eq(self.alu8)

                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.IMMEDIATE.value):
            operand = self.mode_immediate(m)

            with m.If(self.cycle == 2):
                m.d.comb += self.src8_1.eq(self.a)
                m.d.comb += self.src8_2.eq(operand)
                m.d.comb += self.alu8_func.eq(func)

                if store:
                    m.d.ph1 += self.a.eq(self.alu8)

                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE.value):
            operand = self.mode_absolute(m)

            self.read_byte(m, cycle=2, addr=operand, comb_dest=self.src8_2)

            with m.If(self.cycle == 3):
                m.d.comb += self.src8_1.eq(self.a)
                m.d.comb += self.alu8_func.eq(func)

                if store:
                    m.d.ph1 += self.a.eq(self.alu8)

                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.INDIRECT_Y.value):
            self.mode_indirect_y(m)

            with m.If(self.cycle == 5):
                # assign value from input
                m.d.comb += self.src8_2.eq(self.Din)
                m.d.comb += self.src8_1.eq(self.a)
                m.d.comb += self.alu8_func.eq(func)

                if self.verification is not None:
                    self.formal_data.read(m, self.Addr, self.Din)

                if store:
                    m.d.ph1 += self.a.eq(self.alu8)

            # read from corrected address
            with m.If(self.cycle == 6):
                m.d.comb += self.src8_2.eq(self.Din)
                m.d.comb += self.src8_1.eq(self.a)
                m.d.comb += self.alu8_func.eq(func)

                if self.verification is not None:
                    self.formal_data.read(m, self.Addr, self.Din)

                if store:
                    m.d.ph1 += self.a.eq(self.alu8)

                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ZEROPAGE_IND.value):
            operand = self.mode_zeropage_indexed(m, index=self.x)

            self.read_byte(m, cycle=2, addr=operand, comb_dest=self.src8_2)

            with m.If(self.cycle == 3):
                m.d.comb += self.src8_1.eq(self.a)
                m.d.comb += self.alu8_func.eq(func)

                if store:
                    m.d.ph1 += self.a.eq(self.alu8)

                self.end_instr(m, self.pc)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE_Y.value):
            self.mode_absolute_indexed(m, func=func, index=self.y)

        with m.Elif(self.mode_b == AddressModes.ABSOLUTE_X.value):
            self.mode_absolute_indexed(m, func=func, index=self.x)

    # 0x90 BCC branch on carry clear
    # 0xB0 BCS branch on carry set
    # 0xF0 BEQ branch on equal (zero set)

    # 0xD0 BNE branch on not equal (zero clear)

    # 0x10 BPL branch on plus (negative clear)
    # 0x30 BMI branch on minus (negative set)
    # 0x50 BVC branch on overflow clear
    # 0x70 BVS branch on overflow set

    # 76543210
    # aaabbbcc
    # 00010000 BPL
    # 00110000 BMI
    # 01010000 BVC
    # 01110000 BVS
    # 10010000 BCC
    # 10110000 BCS
    # 11010000 BNE
    # 11110000 BEQ

    # "---10000"

    def BR(self, m: Module):
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

    def mode_indirect_x(self, m: Module) -> Statement:
        """Generates logic to get 8-bit operand for indexed indirect addressing instructions.
        """
        value = Mux(self.cycle == 4, self.Din, self.tmp8)

        with m.If(self.cycle == 1):
            # fetch pointer and add X reg
            m.d.ph1 += self.tmp8.eq(self.Din + self.x)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.Addr.eq(self.Din + self.x)
            m.d.ph1 += self.RW.eq(1)
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

        with m.If(self.cycle == 2):
            # read low byte
            m.d.ph1 += self.tmp16l.eq(self.Din)
            m.d.ph1 += self.adh.eq(0)
            m.d.ph1 += self.adl.eq(self.tmp8 + 1)
            m.d.ph1 += self.RW.eq(1)
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

        with m.If(self.cycle == 3):
            # read high byte
            m.d.ph1 += self.tmp16h.eq(self.Din)
            m.d.ph1 += self.adh.eq(self.Din)
            m.d.ph1 += self.adl.eq(self.tmp16l)
            m.d.ph1 += self.RW.eq(1)
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

        with m.If(self.cycle == 4):
            # read value
            m.d.ph1 += self.tmp8.eq(self.Din)
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

        return value

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
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

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
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

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
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

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
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

        with m.If(self.cycle == 2):
            m.d.ph1 += self.tmp16h.eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

        return operand

    def mode_indirect_y(self, m: Module, write: bool = False) -> Statement:
        sum9 = self.tmp16l + self.y
        sum8 = sum9[:8]
        overflow = sum9[8]

        operand = Cat(sum8, self.tmp16h)

        # fetch pointer
        with m.If(self.cycle == 1):
            m.d.ph1 += self.tmp8.eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.adl.eq(self.Din)
            m.d.ph1 += self.adh.eq(0)
            m.d.ph1 += self.RW.eq(1)
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

        # fetch pointer + 1
        with m.If(self.cycle == 2):
            m.d.ph1 += self.tmp16l.eq(self.Din)
            m.d.ph1 += self.adl.eq(self.tmp8 + 1)
            m.d.ph1 += self.adh.eq(0)
            m.d.ph1 += self.RW.eq(1)
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

        with m.If(self.cycle == 3):
            if write:
                m.d.ph1 += self.tmp16h.eq(self.Din + overflow)
            else:
                m.d.ph1 += self.tmp16h.eq(self.Din + overflow)

            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

        with m.If(self.cycle == 4):
            # fix the high byte if overflowed
            if not write:
                m.d.ph1 += self.tmp16h.eq(self.tmp16h + overflow)

            # read byte (invalid if overflowed)
            m.d.ph1 += self.Addr.eq(operand)
            m.d.ph1 += self.RW.eq(1)

            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

        # read from effective address unless page boundery crossed
        # or correcting address
        with m.If(self.cycle == 5):
            with m.If(overflow):
                # prepare to read corrected address
                m.d.ph1 += self.Addr.eq(operand)
                m.d.ph1 += self.RW.eq(1)

                if self.verification is not None:
                    self.formal_data.read(m, self.Addr, self.Din)

            with m.Else():
                if not write:
                    self.end_instr(m, self.pc)

        return operand

    def mode_absolute_indexed(self, m: Module, func: ALU8Func, index: Signal, store: bool = True):
        sum9 = Signal(9)
        overflow = sum9[8]

        # fetch low operand
        with m.If(self.cycle == 1):
            m.d.ph1 += self.tmp16l.eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += self.Addr.eq(self.pc + 1)
            m.d.ph1 += self.RW.eq(1)
            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

        # fetch high operand
        with m.If(self.cycle == 2):
            m.d.ph1 += self.tmp16h.eq(self.Din)
            m.d.ph1 += self.pc.eq(self.pc + 1)
            m.d.ph1 += sum9.eq(self.tmp16l + index)
            m.d.ph1 += self.tmp16l.eq((self.tmp16l + index)[:8])

        with m.If(self.cycle == 3):
            with m.If(overflow):
                # fix the high byte if overflowed
                m.d.ph1 += self.tmp16h.eq(self.tmp16h + 1)
            with m.Else():
                # read effective address
                self.Addr.eq(self.tmp16)
                self.RW.eq(1)

                if self.verification is not None:
                    self.formal_data.read(m, self.Addr, self.Din)

        with m.If(self.cycle == 4):
            with m.If(overflow):
                # read effective address
                self.Addr.eq(self.tmp16)
                self.RW.eq(1)

                if self.verification is not None:
                    self.formal_data.read(m, self.Addr, self.Din)

            with m.Else():
                # assign readed value
                m.d.comb += self.src8_2.eq(self.Din)
                m.d.comb += self.src8_1.eq(self.a)
                m.d.comb += self.alu8_func.eq(func)

                if self.verification is not None:
                    self.formal_data.read(m, self.Addr, self.Din)

                if store:
                    m.d.ph1 += self.a.eq(self.alu8)

                self.end_instr(m, self.pc)

        # read from corrected address
        with m.If(self.cycle == 5):
            with m.If(overflow):
                m.d.comb += self.src8_2.eq(self.Din)
                m.d.comb += self.src8_1.eq(self.a)
                m.d.comb += self.alu8_func.eq(func)

                if self.verification is not None:
                    self.formal_data.read(m, self.Addr, self.Din)

                if store:
                    m.d.ph1 += self.a.eq(self.alu8)

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

            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

        with m.If(self.cycle == 3):
            m.d.ph1 += self.pcl.eq(self.Din)

            m.d.ph1 += self.adl.eq(pointer[:8] + 1)
            m.d.ph1 += self.adh.eq(pointer[8:])
            m.d.ph1 += self.RW.eq(1)

            if self.verification is not None:
                self.formal_data.read(m, self.Addr, self.Din)

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
            m.d.ph1 += Cover(core.formal_data.snapshot_taken &
                             core.end_instr_flag)
            m.d.ph1 += Assume(core.formal_data.snapshot_taken &
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
