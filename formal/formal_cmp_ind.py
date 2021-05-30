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


CPX = "111---00"
CPY = "110---00"


class Formal(AluVerification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(
            0xE0, 0xE4, 0xEC,
            0xC0, 0xC4, 0xCC
        )

    def check(self, m: Module):
        with m.If(self.instr.matches(CPX)):
            with m.If(self.instr.matches(0xE0)):
                self.assert_cycles(m, 2)
                value = self.assert_cycle_signals(
                    m, 1, address=self.data.pre_pc+1, rw=1)
                input1 = Signal(8)
                input2 = Signal(8)
                m.d.comb += input1.eq(self.data.pre_x)
                m.d.comb += input2.eq(value)
                z = (input1 == input2)
                n = (input1 - input2)[7]
                c = (input1 < input2)
                self.assert_registers(m, PC=self.data.pre_pc+2)
                self.assertFlags(m, Z=z, N=n, C=c)
            with m.Else():
                input1, input2, actual_output, size = self.common_check(m,
                    input=self.data.pre_x,
                    x_index=self.data.pre_y,
                    output=self.data.post_x)
                z = (input1 == input2)
                n = (input1 - input2)[7]
                c = (input1 < input2)
                self.assert_registers(m, PC=self.data.pre_pc+size)
                self.assertFlags(m, Z=z, N=n, C=c)
        with m.Elif(self.instr.matches(CPY)):
            with m.If(self.instr.matches(0xC0)):
                self.assert_cycles(m, 2)
                value = self.assert_cycle_signals(
                    m, 1, address=self.data.pre_pc+1, rw=1)
                input1 = Signal(8)
                input2 = Signal(8)
                m.d.comb += input1.eq(self.data.pre_y)
                m.d.comb += input2.eq(value)
                z = (input1 == input2)
                n = (input1 - input2)[7]
                c = (input1 < input2)
                self.assert_registers(m, PC=self.data.pre_pc+2)
                self.assertFlags(m, Z=z, N=n, C=c)
            with m.Else():
                input1, input2, actual_output, size = self.common_check(m,
                    input=self.data.pre_y,
                    x_index=self.data.pre_x,
                    output=self.data.post_y)
                z = (input1 == input2)
                n = (input1 - input2)[7]
                c = (input1 < input2)
                self.assert_registers(m, PC=self.data.pre_pc+size)
                self.assertFlags(m, Z=z, N=n, C=c)
