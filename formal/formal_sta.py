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

from nmigen import Signal, Value, Cat, Module, Const
from nmigen.asserts import Assert
from .verification import Verification
from consts import AddressModes


class Formal(Verification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches(0x85, 0x95, 0x8D, 0x9D, 0x99, 0x81, 0x91)

    def check(self, m: Module):
        mode = self.instr[2:5]

        with m.If(mode == AddressModes.ZEROPAGE.value):
            self.assert_cycles(m, 3)
            zp = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            value = self.assert_cycle_signals(
                m, 2, address=zp, rw=0)
            m.d.comb += Assert(value == self.data.pre_a)
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
            m.d.comb += Assert(value == self.data.pre_a)
            self.assert_registers(m, PC=self.data.pre_pc+2)

        with m.Elif(mode == AddressModes.ABSOLUTE.value):
            self.assert_cycles(m, 4)
            addr_lo = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            addr_hi = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc+2, rw=1)
            value = self.assert_cycle_signals(
                m, 3, address=Cat(addr_lo, addr_hi), rw=0)
            m.d.comb += Assert(value == self.data.pre_a)
            self.assert_registers(m, PC=self.data.pre_pc+3)

        with m.Elif(mode == AddressModes.ABSOLUTE_X.value):
            self.assert_cycles(m, 5)
            addr_lo = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            addr_hi = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc+2, rw=1)
            sum9 = Signal(9)
            m.d.comb += sum9.eq(addr_lo + self.data.pre_x)
            addr_abs = Cat(sum9[:8], addr_hi)
            addr_corrected = Cat(sum9[:8], addr_hi + sum9[8])
            self.assert_cycle_signals(
                m, 3, address=addr_abs, rw=1)
            value = self.assert_cycle_signals(
                m, 4, address=addr_corrected, rw=0)
            m.d.comb += Assert(value == self.data.pre_a)
            self.assert_registers(m, PC=self.data.pre_pc+3)

        with m.Elif(mode == AddressModes.ABSOLUTE_Y.value):
            self.assert_cycles(m, 5)
            addr_lo = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            addr_hi = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc+2, rw=1)
            sum9 = Signal(9)
            m.d.comb += sum9.eq(addr_lo + self.data.pre_y)
            addr_abs = Cat(sum9[:8], addr_hi)
            addr_corrected = Cat(sum9[:8], addr_hi + sum9[8])
            self.assert_cycle_signals(
                m, 3, address=addr_abs, rw=1)
            value = self.assert_cycle_signals(
                m, 4, address=addr_corrected, rw=0)
            m.d.comb += Assert(value == self.data.pre_a)
            self.assert_registers(m, PC=self.data.pre_pc+3)

        with m.Elif(mode == AddressModes.INDIRECT_X.value):
            self.assert_cycles(m, 6)
            zp = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc + 1, rw=1)
            ind_lo = (zp + self.data.pre_x)[:8]
            ind_hi = (ind_lo + 1)[:8]
            addr_lo = self.assert_cycle_signals(
                m, 2, address=ind_lo, rw=1)
            addr_hi = self.assert_cycle_signals(
                m, 3, address=ind_hi, rw=1)
            self.assert_cycle_signals(
                m, 4, address=Cat(addr_lo, addr_hi), rw=1)
            value = self.assert_cycle_signals(
                m, 5, address=Cat(addr_lo, addr_hi), rw=0)
            m.d.comb += Assert(value == self.data.pre_a)
            self.assert_registers(m, PC=self.data.pre_pc+2)

        with m.Elif(mode == AddressModes.INDIRECT_Y.value):
            self.assert_cycles(m, 6)
            zp = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            addr_lo = self.assert_cycle_signals(
                m, 2, address=zp, rw=1)
            addr_hi = self.assert_cycle_signals(
                m, 3, address=(zp+1)[:8], rw=1)
            sum9 = addr_lo + self.data.pre_y
            addr_ind_lo = sum9[:8]
            overflow = sum9[8]
            addr_ind_hi = (addr_hi + overflow)[:8]
            self.assert_cycle_signals(
                m, 4, address=Cat(addr_ind_lo, addr_hi), rw=1)
            value = self.assert_cycle_signals(
                m, 5, address=Cat(addr_ind_lo, addr_ind_hi), rw=0)
            m.d.comb += Assert(value == self.data.pre_a)
            self.assert_registers(m, PC=self.data.pre_pc+2)
