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

from nmigen import Signal, Value, Cat, Module, signed, Mux
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert
from .verification import FormalData, Verification
from .alu_verification import AluVerification, Alu2Verification
from consts import Flags


INC = "111---10"
DEC = "110---10"


class Formal(Alu2Verification):
    def __init__(self):
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches(
            0xE6,0xEE,0xF6,0xFE,
            0xC6,0xCE,0xD6,0xDE
        )

    def check(self, m: Module, instr: Value, data: FormalData):
        input, actual_output = self.common_check(m, instr, data)
        expected_output = Signal(8)

        n = expected_output[7]
        z = (expected_output == 0)

        with m.If(instr.matches(INC)):
            m.d.comb += [
                expected_output.eq(input + 1),
                Assert(actual_output == expected_output)
            ]

        with m.Elif(instr.matches(DEC)):
            m.d.comb += [
                expected_output.eq(input - 1),
                Assert(actual_output == expected_output)
            ]

        self.assertFlags(m, data.post_sr_flags, data.pre_sr_flags, N=n, Z=z)
