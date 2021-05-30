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

from nmigen import Const, Signal, Value, Cat, Module
from .verification import Verification
from consts import Flags


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(0x60)

    def check(self, m: Module):
        self.assert_cycles(m, 6)

        self.assert_cycle_signals(
            m, 1, address=self.data.pre_pc+1, rw=1)

        self.assert_cycle_signals(
            m, 2, address=Cat(self.data.pre_sp, Const(1, 8)), rw=1)

        addr_lo = self.assert_cycle_signals(
            m, 3, address=Cat((self.data.pre_sp + 1)[:8], Const(1, 8)), rw=1)

        addr_hi = self.assert_cycle_signals(
            m, 4, address=Cat((self.data.pre_sp + 2)[:8], Const(1, 8)), rw=1)

        new_pc = Cat(addr_lo, addr_hi)

        self.assert_registers(m, SP=self.data.pre_sp+2, PC=new_pc)
        self.assertFlags(m)
