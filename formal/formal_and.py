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

from nmigen import Signal, Value, Cat, Module
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert
from .verification import FormalData, Verification
from .alu_verification import AluVerification


class Formal(AluVerification):
    def __init__(self):
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches("001---01")

    def check(self, m: Module, instr: Value, data: FormalData):
        input1, input2, actual_output = self.common_check(m, instr, data)
        and_o = Signal(8)

        n = and_o[7]
        z = (and_o == 0)

        m.d.comb += [
            and_o.eq(input1 & input2),
            Assert(actual_output == and_o),
        ]
        self.assertFlags(m, data.post_sr_flags, data.pre_sr_flags,
                         Z=z, N=n)
