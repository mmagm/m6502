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
from .verification import Verification
from consts import Flags

class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(
            0xAA, 0xA8, 0xBA, 0x8A, 0x9A, 0x98
        )

    def check(self, m: Module):
        self.assert_cycles(m, 2)

        with m.Switch(self.instr):
            with m.Case(0xAA):
                # TAX
                self.assert_registers(m, X=self.data.pre_a, PC=self.data.pre_pc + 1)
                z = self.data.post_a == 0
                n = self.data.post_a[7]
                self.assertFlags(m, Z=z, N=n)
            with m.Case(0xA8):
                # TAY
                self.assert_registers(m, Y=self.data.pre_a, PC=self.data.pre_pc + 1)
                z = self.data.pre_a == 0
                n = self.data.pre_a[7]
                self.assertFlags(m, Z=z, N=n)
            with m.Case(0xBA):
                # TSX
                self.assert_registers(m, X=self.data.pre_sp, PC=self.data.pre_pc + 1)
                z = self.data.pre_sp == 0
                n = self.data.pre_sp[7]
                self.assertFlags(m, Z=z, N=n)
            with m.Case(0x8A):
                # TXA
                self.assert_registers(m, A=self.data.pre_x, PC=self.data.pre_pc + 1)
                z = self.data.pre_x == 0
                n = self.data.pre_x[7]
                self.assertFlags(m, Z=z, N=n)
            with m.Case(0x9A):
                # TXS
                self.assert_registers(m, SP=self.data.pre_x, PC=self.data.pre_pc + 1)
            with m.Case(0x98):
                # TYA
                self.assert_registers(m, A=self.data.pre_y, PC=self.data.pre_pc + 1)
                z = self.data.pre_y == 0
                n = self.data.pre_y[7]
                self.assertFlags(m, Z=z, N=n)
