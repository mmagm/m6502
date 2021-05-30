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

from nmigen import Signal, Value, Module
from .alu_verification import AluVerification
from consts import Flags


LDX = "101---10"
LDY = "101---00"


class Formal(AluVerification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(
            0xA2, 0xA6, 0xB6, 0xAE, 0xBE,
            0xA0, 0xA4, 0xB4, 0xAC, 0xBC
        )

    def check(self, m: Module):
        with m.If(self.instr.matches(LDX)):
            with m.If(self.instr.matches(0xA2)):
                self.assert_cycles(m, 2)
                output = self.assert_cycle_signals(
                    m, 1, address=self.data.pre_pc+1, rw=1)
                z = output == 0
                n = output[7]
                self.assert_registers(m, X=output, PC=self.data.pre_pc+2)
                self.assertFlags(m, Z=z, N=n)
            with m.Else():
                _, input2, actual_output, size = self.common_check(m,
                    input=self.data.pre_x,
                    x_index=self.data.pre_y,
                    output=self.data.post_x)

                output = input2

                z = output == 0
                n = output[7]

                self.assert_registers(m, X=output, PC=self.data.pre_pc+size)
                self.assertFlags(m, Z=z, N=n)
        with m.Elif(self.instr.matches(LDY)):
            with m.If(self.instr.matches(0xA0)):
                self.assert_cycles(m, 2)
                output = self.assert_cycle_signals(
                    m, 1, address=self.data.pre_pc+1, rw=1)
                z = output == 0
                n = output[7]
                self.assert_registers(m, Y=output, PC=self.data.pre_pc+2)
                self.assertFlags(m, Z=z, N=n)
            with m.Else():
                _, input2, actual_output, size = self.common_check(m,
                    input=self.data.pre_y,
                    x_index=self.data.pre_x,
                    output=self.data.post_y)

                output = input2

                z = output == 0
                n = output[7]

                self.assert_registers(m, Y=output, PC=self.data.pre_pc+size)
                self.assertFlags(m, Z=z, N=n)
