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

from typing import Tuple

from nmigen import Signal, Value, Cat, Module, Mux, Const, unsigned
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert, Assume
from .verification import FormalData, Verification
from consts import AddressModes


class AluVerification(Verification):
    def __init__(self):
        pass

    def common_check(self, m: Module, instr: Value, data: FormalData) -> Tuple[Value, Value, Value]:
        """Does common checks for ALU instructions.

        Returns a tuple of values: (input1, input2, actual_output). The caller should use those
        values to verify flags and expected output.
        """
        mode = instr[2:5]

        input1 = data.pre_a
        input2 = Signal(8)
        actual_output = data.post_a

        m.d.comb += [
            Assert(data.post_x == data.pre_x),
            Assert(data.post_y == data.pre_y),
            Assert(data.post_sp == data.pre_sp),
            Assert(data.addresses_written == 0),
        ]

        with m.If(mode == AddressModes.INDIRECT_X.value):
            m.d.comb += [
                Assert(data.post_pc == data.plus16(data.pre_pc, 2)),
                Assert(data.addresses_read == 4),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                input2.eq(data.read_data[3])
            ]

        with m.If(mode == AddressModes.ZEROPAGE.value):
            m.d.comb += [
                Assert(data.post_pc == data.plus16(data.pre_pc, 2)),
                Assert(data.addresses_read == 2),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                Assert(data.read_addr[1] == data.read_data[0]),
                input2.eq(data.read_data[1]),
            ]

        with m.Elif(mode == AddressModes.ABSOLUTE.value):
            m.d.comb += [
                Assert(data.post_pc == data.plus16(data.pre_pc, 3)),
                Assert(data.addresses_read == 3),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                Assert(data.read_addr[1] == data.plus16(data.pre_pc, 2)),
                Assert(data.read_addr[2] == Cat(data.read_data[0], data.read_data[1])),
                input2.eq(data.read_data[2]),
            ]

        with m.Elif(mode == AddressModes.IMMEDIATE.value):
            m.d.comb += [
                Assert(data.post_pc == data.plus16(data.pre_pc, 2)),
                Assert(data.addresses_read == 1),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                input2.eq(data.read_data[0]),
            ]

        with m.Elif(mode == AddressModes.ZEROPAGE_X.value):
            m.d.comb += [
                Assert(data.post_pc == data.plus16(data.pre_pc, 2)),
                Assert(data.addresses_read == 2),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                input2.eq(data.read_data[1]),
            ]

        with m.Elif(mode == AddressModes.INDIRECT_Y.value):
            m.d.comb += [
                Assert(data.post_pc == data.plus16(data.pre_pc, 2)),
                Assert(data.addresses_read == 4),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                input2.eq(data.read_data[3]),
            ]

        with m.Elif(mode == AddressModes.ABSOLUTE_X.value):
            m.d.comb += [
                Assert(data.post_pc == data.plus16(data.pre_pc, 3)),
                Assert(data.addresses_read == 3),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                Assert(data.read_addr[1] == data.plus16(data.pre_pc, 2)),
                input2.eq(data.read_data[2]),
            ]

        with m.Elif(mode == AddressModes.ABSOLUTE_Y.value):
            m.d.comb += [
                Assert(data.post_pc == data.plus16(data.pre_pc, 3)),
                Assert(data.addresses_read == 3),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                Assert(data.read_addr[1] == data.plus16(data.pre_pc, 2)),
                input2.eq(data.read_data[2]),
            ]

        return (input1, input2, actual_output)
