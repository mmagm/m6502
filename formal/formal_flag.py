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

from nmigen import Signal, Value, Cat, Module, signed, Mux, Const, Array
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert
from .verification import FormalData, Verification
from consts import Flags

CLC = 0x18 # "00011000"
SEC = 0x38 # "00111000"
CLD = 0xD8 # "11011000"
SED = 0xF8 # "11111000"
CLI = 0x58 # "01011000"
SEI = 0x78 # "01111000"
CLV = 0xB8 # "10111000"


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(CLC, SEC, CLD, SED, CLI, SEI, CLV)

    def check(self, m: Module):
        self.assert_cycles(m, 2)

        c = Signal()
        d = Signal()
        i = Signal()
        v = Signal()

        m.d.comb += c.eq(self.data.pre_sr_flags[Flags.C])
        m.d.comb += d.eq(self.data.pre_sr_flags[Flags.D])
        m.d.comb += i.eq(self.data.pre_sr_flags[Flags.I])
        m.d.comb += v.eq(self.data.pre_sr_flags[Flags.V])

        with m.Switch(self.instr):
            with m.Case(CLC):
                m.d.comb += c.eq(0)
            with m.Case(SEC):
                m.d.comb += c.eq(1)
            with m.Case(CLD):
                m.d.comb += d.eq(0)
            with m.Case(SED):
                m.d.comb += d.eq(1)
            with m.Case(CLI):
                m.d.comb += i.eq(0)
            with m.Case(SEI):
                m.d.comb += i.eq(1)
            with m.Case(CLV):
                m.d.comb += v.eq(0)

        self.assertFlags(m, C=c, D=d, I=i, V=v)
        self.assert_registers(m, PC=self.data.pre_pc+1)
