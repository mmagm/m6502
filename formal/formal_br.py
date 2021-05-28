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

from enum import IntEnum

from nmigen import Signal, Value, Cat, Module, signed, Mux, Const, Array
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert
from .verification import FormalData, Verification
from consts import Flags


class Branch(IntEnum):
    PL = 0
    MI = 1
    VC = 2
    VS = 3
    CC = 4
    CS = 5
    NE = 6
    EQ = 7


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches("---10000")

    def check(self, m: Module):
        operand = self.assert_cycle_signals(
            m, 1, address=self.data.pre_pc+1, rw=1)

        n = self.data.pre_sr_flags[Flags.N]
        v = self.data.pre_sr_flags[Flags.V]
        c = self.data.pre_sr_flags[Flags.C]
        z = self.data.pre_sr_flags[Flags.Z]

        take_branch = Array([
            n == 0,
            n == 1,
            v == 0,
            v == 1,
            c == 0,
            c == 1,
            z == 0,
            z == 1,
        ])

        mode_a = self.instr[5:8]

        pre_pc = Signal(16)
        m.d.comb += pre_pc.eq(self.data.pre_pc + 2)

        sum9 = Signal(9)
        m.d.comb += sum9.eq(pre_pc[:8] + operand)

        co = sum9[8]
        backwards = operand[7]

        crossed = Signal()
        m.d.comb += crossed.eq(co ^ backwards)

        with m.If(take_branch[mode_a]):
            with m.If(crossed):
                self.assert_cycles(m, 4)
                with m.If(backwards):
                    self.assert_registers(m, PC=Cat(sum9[:8], (pre_pc[8:] - 1)[:8]))
                with m.Else():
                    self.assert_registers(m, PC=Cat(sum9[:8], (pre_pc[8:] + 1)[:8]))
            with m.Else():
                self.assert_cycles(m, 3)
                self.assert_registers(m, PC=Cat(sum9[:8], pre_pc[8:]))
        with m.Else():
            self.assert_cycles(m, 2)
            self.assert_registers(m, PC=pre_pc)
