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


PLA = 0x68
PLP = 0x28


class Formal(AluVerification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(
            0x68, 0x28
        )

    def check(self, m: Module):
        self.assert_cycles(m, 4)

        address = Signal(16)

        m.d.comb += address[:8].eq(self.data.pre_sp + 1)
        m.d.comb += address[8:].eq(1)

        value = self.assert_cycle_signals(
            m, 3, address=address, rw=1)

        with m.If(self.instr.matches(PLA)):
            n = value[7]
            z = value == 0

            self.assertFlags(m, Z=z, N=n)
            self.assert_registers(m, A=value, SP=self.data.pre_sp+1, PC=self.data.pre_pc+1)

        with m.If(self.instr.matches(PLP)):
            self.assertFlags(
                m,
                N=value[Flags.N],
                V=value[Flags.V],
                B=value[Flags.B],
                D=value[Flags.D],
                I=value[Flags.I],
                Z=value[Flags.Z],
                C=value[Flags.C]
            )
            self.assert_registers(m, SP=self.data.pre_sp+1, PC=self.data.pre_pc+1)
