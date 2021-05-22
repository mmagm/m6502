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

from nmigen import Const, Signal, Value, Cat, Module, signed, Mux, unsigned
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert
from .verification import FormalData, Verification
from .alu_verification import AluVerification, Alu2Verification
from consts import Flags


PHA = 0x48
PHP = 0x08


class Formal(AluVerification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(
            0x48, 0x08
        )

    def check(self, m: Module):
        self.assert_cycles(m, 3)

        value = self.assert_cycle_signals(
            m, 2, address=Cat(self.data.pre_sp, Const(0x01, 8)), rw=0)

        with m.If(self.instr.matches(PHA)):
            m.d.comb += Assert(value == self.data.pre_a)

        with m.Elif(self.instr.matches(PHP)):
            m.d.comb += Assert(value == self.data.pre_sr_flags)

        self.assert_registers(m, SP=self.data.pre_sp-1, PC=self.data.pre_pc+1)
