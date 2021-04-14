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


class Branch(IntEnum):
    PL = 0
    MI = 1
    VC = 2
    VS = 3
    CC = 4
    CS = 5
    NE = 6
    EQ = 7


class Formal(Verification):
    def __init__(self):
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches("---10000")

    def check(self, m: Module, instr: Value, data: FormalData):
        m.d.comb += [
            Assert(data.post_sr_flags == data.pre_sr_flags),
            Assert(data.post_a == data.pre_a),
            Assert(data.post_x == data.pre_x),
            Assert(data.post_y == data.pre_y),
            Assert(data.post_sp == data.pre_sp),
            Assert(data.addresses_written == 0),
        ]

        m.d.comb += [
            Assert(data.addresses_read == 1),
            Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
        ]

        n = data.pre_sr_flags[Flags.N]
        v = data.pre_sr_flags[Flags.V]
        c = data.pre_sr_flags[Flags.C]
        z = data.pre_sr_flags[Flags.Z]

        take_branch = Array([
            n == 0,
            n == 1,
            v == 0,
            v == 1,
            c == 0,
            c == 1,
            z == 0,
            z == 1,
        ])

        mode_a = instr[5:8]

        operand = data.read_data[0]

        pre_pc = Signal(16)

        m.d.comb += pre_pc.eq(data.pre_pc + 2)

        sum9 = Signal(9)
        m.d.comb += sum9.eq(pre_pc[:8] + operand)

        co = sum9[8]
        backwards = operand[7]

        crossed = Signal()
        m.d.comb += crossed.eq(co ^ backwards)

        with m.If(take_branch[mode_a]):
            m.d.comb += Assert(data.post_pc[:8] == sum9[:8])

            with m.If(crossed):
                with m.If(backwards):
                    m.d.comb += Assert(data.post_pc[8:] == (pre_pc[8:] - 1)[:8])
                with m.Else():
                    m.d.comb += Assert(data.post_pc[8:] == (pre_pc[8:] + 1)[:8])
            with m.Else():
                m.d.comb += Assert(data.post_pc[8:] == pre_pc[8:])
        with m.Else():
            m.d.comb += Assert(data.post_pc == pre_pc)
