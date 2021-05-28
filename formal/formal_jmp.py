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


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches("01-01100")

    def check(self, m: Module):
        mode_a = self.instr[5:8]

        self.assertFlags(m)

        with m.If(mode_a == 2):
            self.assert_cycles(m, 3)
            addr_lo = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            addr_hi = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc+2, rw=1)
            self.assert_registers(m, PC=Cat(addr_lo, addr_hi))

        with m.Elif(mode_a == 3):
            self.assert_cycles(m, 5)

            pointer_lo = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            pointer_hi = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc+2, rw=1)

            addr_lo = self.assert_cycle_signals(
                m, 3, address=Cat(pointer_lo, pointer_hi), rw=1)

            addr_hi = self.assert_cycle_signals(
                m, 4, address=Cat((pointer_lo + 1)[:8], pointer_hi), rw=1)

            self.assert_registers(m, PC=Cat(addr_lo, addr_hi))
