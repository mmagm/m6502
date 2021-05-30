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
from .verification import Verification
from consts import Flags


INX = 0xE8
INY = 0xC8
DEX = 0xCA
DEY = 0x88


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(
            0xE8,0xC8,0xCA,0x88
        )

    def check(self, m: Module):
        input = Signal(8)
        output = Signal(8)

        n = output[7]
        z = (output == 0)

        self.assert_cycles(m, 2)

        with m.If(self.instr.matches(INX)):
            m.d.comb += input.eq(self.data.pre_x)
            m.d.comb += output.eq(input + 1)
            self.assert_registers(m, X=output, PC=self.data.pre_pc+1)
        with m.If(self.instr.matches(INY)):
            m.d.comb += input.eq(self.data.pre_y)
            m.d.comb += output.eq(input + 1)
            self.assert_registers(m, Y=output, PC=self.data.pre_pc+1)
        with m.Elif(self.instr.matches(DEX)):
            m.d.comb += input.eq(self.data.pre_x)
            m.d.comb += output.eq(input - 1)
            self.assert_registers(m, X=output, PC=self.data.pre_pc+1)
        with m.Elif(self.instr.matches(DEY)):
            m.d.comb += input.eq(self.data.pre_y)
            m.d.comb += output.eq(input - 1)
            self.assert_registers(m, Y=output, PC=self.data.pre_pc+1)

        self.assertFlags(m, Z=z, N=n)
