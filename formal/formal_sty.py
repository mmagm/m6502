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

from nmigen import Signal, Value, Cat, Module, Mux
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert, Assume
from .verification import FormalData, Verification
from consts import AddressModes


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(0x84,0x94,0x8C)

    def check(self, m: Module):
        mode = self.instr[2:5]

        with m.If(mode == AddressModes.ZEROPAGE.value):
            self.assert_cycles(m, 3)
            zp = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            value = self.assert_cycle_signals(
                m, 2, address=zp, rw=0)
            m.d.comb += Assert(value == self.data.pre_y)
            self.assert_registers(m, PC=self.data.pre_pc+2)

        with m.Elif(mode == AddressModes.ZEROPAGE_IND.value):
            self.assert_cycles(m, 4)
            zp = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            self.assert_cycle_signals(
                m, 2, address=zp, rw=1)
            zp_ind = (zp + self.data.pre_x)[:8]
            value = self.assert_cycle_signals(
                m, 3, address=zp_ind, rw=0)
            m.d.comb += Assert(value == self.data.pre_y)
            self.assert_registers(m, PC=self.data.pre_pc+2)


        with m.Elif(mode == AddressModes.ABSOLUTE.value):
            self.assert_cycles(m, 4)
            addr_lo = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            addr_hi = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc+2, rw=1)
            value = self.assert_cycle_signals(
                m, 3, address=Cat(addr_lo, addr_hi), rw=0)
            m.d.comb += Assert(value == self.data.pre_y)
            self.assert_registers(m, PC=self.data.pre_pc+3)
