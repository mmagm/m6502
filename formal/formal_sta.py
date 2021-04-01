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

from nmigen import Signal, Value, Cat, Module, Mux
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert
from .verification import FormalData, Verification


class Formal(Verification):
    def __init__(self):
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches(0x8D)

    def check(self, m: Module, instr: Value, data: FormalData):
        written_data = data.pre_a

        m.d.comb += [
            Assert(data.post_sr_flags == data.pre_sr_flags),
            Assert(data.post_a == data.pre_a),
            Assert(data.post_x == data.pre_x),
            Assert(data.post_y == data.pre_y),
            Assert(data.post_sp == data.pre_sp),
        ]
        m.d.comb += [
            Assert(data.post_pc == data.plus16(data.pre_pc, 3)),

            Assert(data.addresses_read == 2),
            Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
            Assert(data.read_addr[1] == data.plus16(data.pre_pc, 2)),

            Assert(data.addresses_written == 1),
            Assert(data.write_addr[0] == Cat(data.read_data[1], data.read_data[0])),

            Assert(data.write_data[0] == written_data),
        ]
