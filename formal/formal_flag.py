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
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches(CLC, SEC, CLD, SED, CLI, SEI, CLV)

    def check(self, m: Module, instr: Value, data: FormalData):
        m.d.comb += [
            Assert(data.post_a == data.pre_a),
            Assert(data.post_x == data.pre_x),
            Assert(data.post_y == data.pre_y),
            Assert(data.post_sp == data.pre_sp),
            Assert(data.addresses_read == 0),
            Assert(data.addresses_written == 0)
        ]

        m.d.comb += Assert(data.post_pc == data.plus16(data.pre_pc, 1))

        c = Signal()
        d = Signal()
        i = Signal()
        v = Signal()

        m.d.comb += c.eq(data.pre_sr_flags[Flags.C])
        m.d.comb += d.eq(data.pre_sr_flags[Flags.D])
        m.d.comb += i.eq(data.pre_sr_flags[Flags.I])
        m.d.comb += v.eq(data.pre_sr_flags[Flags.V])

        with m.Switch(instr):
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

        self.assertFlags(m, data.post_sr_flags, data.pre_sr_flags, C=c, D=d, I=i, V=v)
