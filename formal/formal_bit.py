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

from nmigen import Signal, Value, Module
from .alu_verification import AluVerification


class Formal(AluVerification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches("0010-100")

    def check(self, m: Module):
        input1, input2, actual_output, size = self.common_check(m)

        output = input1

        flag_output = input1 & input2
        z = flag_output == 0
        n = flag_output[7]

        self.assert_registers(m, PC=self.data.pre_pc+size)
        self.assertFlags(m, Z=z, N=n)
