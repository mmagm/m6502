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

from typing import Tuple

from nmigen import Signal, Value, Cat, Module, Mux, Const, unsigned
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert, Assume
from .verification import FormalData, Verification
from consts import AddressModes


class AluVerification(Verification):
    def __init__(self):
        super().__init__()

    def common_check(self, m: Module) -> Tuple[Value, Value, Value]:
        """Does common checks for ALU instructions.

        Returns a tuple of values: (input1, input2, actual_output, size). The caller should use those
        values to verify flags and expected output.
        """
        mode = self.instr[2:5]

        input1 = self.data.pre_a
        input2 = Signal(8)
        actual_output = self.data.post_a
        size = Signal(3)

        with m.If(mode == AddressModes.INDIRECT_X.value):
            self.assert_cycles(m, 6)
            zp = self.assert_cycle_signals(
                m, 1, rw=1, address=self.data.pre_pc + 1
            )
            addr_ind = (zp + self.data.pre_x)[:8]
            addr_lo = self.assert_cycle_signals(
                m, 2, rw=1, address=addr_ind
            )
            addr_hi = self.assert_cycle_signals(
                m, 3, rw=1, address=(addr_ind + 1)[:8]
            )
            value = self.assert_cycle_signals(
                m, 4, rw=1, address=Cat(addr_lo, addr_hi)
            )
            m.d.comb += input2.eq(value)
            m.d.comb += size.eq(2)

        with m.If(mode == AddressModes.ZEROPAGE.value):
            self.assert_cycles(m, 3)
            addr_lo = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            value = self.assert_cycle_signals(
                m, 2, address=addr_lo, rw=1)
            m.d.comb += input2.eq(value)
            m.d.comb += size.eq(2)

        with m.Elif(mode == AddressModes.ABSOLUTE.value):
            self.assert_cycles(m, 4)
            addr_lo = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            addr_hi = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc+2, rw=1)
            value = self.assert_cycle_signals(
                m, 3, address=Cat(addr_lo, addr_hi), rw=1)
            m.d.comb += input2.eq(value)
            m.d.comb += size.eq(3)

        with m.Elif(mode == AddressModes.IMMEDIATE.value):
            self.assert_cycles(m, 3)
            value = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            m.d.comb += input2.eq(value)
            m.d.comb += size.eq(2)

        with m.Elif(mode == AddressModes.ZEROPAGE_IND.value):
            self.assert_cycles(m, 4)
            zp = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            value = self.assert_cycle_signals(
                m, 3, address=Cat(zp + self.data.pre_x, 0x00), rw=1)
            m.d.comb += input2.eq(value)
            m.d.comb += size.eq(2)

        with m.Elif(mode == AddressModes.INDIRECT_Y.value):
            zp = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            addr_lo = self.assert_cycle_signals(
                m, 2, address=zp, rw=1)
            addr_hi = self.assert_cycle_signals(
                m, 3, address=(zp+1)[:8], rw=1)
            addr_ind_lo = (addr_lo + self.data.pre_y)[:8]
            crossed = (addr_lo + self.data.pre_y)[8]
            value = self.assert_cycle_signals(
                m, 4, address=Cat(addr_ind_lo, addr_hi), rw=1)

            with m.If(crossed):
                corrected_value = self.assert_cycle_signals(
                    m, 5, address=Cat(addr_ind_lo, (addr_hi + crossed)[:8]), rw=1)
                self.assert_cycles(m, 6)
                m.d.comb += input2.eq(corrected_value)

            with m.Else():
                self.assert_cycles(m, 5)
                m.d.comb += input2.eq(value)

            m.d.comb += size.eq(2)

        with m.Elif(mode == AddressModes.ABSOLUTE_X.value):
            addr_lo = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            addr_hi = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc+2, rw=1)
            addr_ind_lo = (addr_lo + self.data.pre_x)[:8]
            crossed = (addr_lo + self.data.pre_x)[8]
            value = self.assert_cycle_signals(
                m, 3, address=Cat(addr_ind_lo, addr_hi), rw=1)

            with m.If(crossed):
                corrected_value = self.assert_cycle_signals(
                    m, 4, address=Cat(addr_ind_lo, (addr_hi + crossed)[:8]))
                self.assert_cycles(m, 5)
                m.d.comb += input2.eq(corrected_value)
            with m.Else():
                self.assert_cycles(m, 4)
                m.d.comb += input2.eq(value)

            m.d.comb += size.eq(3)

        with m.Elif(mode == AddressModes.ABSOLUTE_Y.value):
            addr_lo = self.assert_cycle_signals(
                m, 1, address=self.data.pre_pc+1, rw=1)
            addr_hi = self.assert_cycle_signals(
                m, 2, address=self.data.pre_pc+2, rw=1)
            addr_ind_lo = (addr_lo + self.data.pre_y)[:8]
            crossed = (addr_lo + self.data.pre_y)[8]
            value = self.assert_cycle_signals(
                m, 3, address=Cat(addr_ind_lo, addr_hi), rw=1)

            with m.If(crossed):
                corrected_value = self.assert_cycle_signals(
                    m, 4, address=Cat(addr_ind_lo, (addr_hi + crossed)[:8]))
                self.assert_cycles(m, 5)
                m.d.comb += input2.eq(corrected_value)
            with m.Else():
                self.assert_cycles(m, 4)
                m.d.comb += input2.eq(value)

            m.d.comb += size.eq(3)

        return (input1, input2, actual_output, size)


class Alu2Verification(Verification):
    def __init__(self):
        pass

    def common_check(self, m: Module, instr: Value, data: FormalData) -> Tuple[Value, Value, Value]:
        mode = instr[2:5]
        input = Signal(8)
        actual_output = Signal(8)
        size = Signal(3)

        m.d.comb += [
            Assert(data.post_x == data.pre_x),
            Assert(data.post_y == data.pre_y),
            Assert(data.post_sp == data.pre_sp)
        ]

        with m.If(mode == AddressModes.IMMEDIATE.value):
            m.d.comb += [
                Assert(data.post_pc == data.plus16(data.pre_pc, 1)),
                Assert(data.addresses_read == 1),
                Assert(data.addresses_written == 0),
                input.eq(data.pre_a)
            ]

            m.d.comb += actual_output.eq(data.post_a)

        with m.Elif(mode == AddressModes.ZEROPAGE.value):
            m.d.comb += [
                Assert(data.post_a == data.pre_a),
                Assert(data.post_pc == data.plus16(data.pre_pc, 2)),
                Assert(data.addresses_read == 2),
                Assert(data.read_addr[1] == Cat(data.read_data[0], 0x00)),
                input.eq(data.read_data[1])
            ]

            m.d.comb += [
                Assert(data.addresses_written == 2),
                Assert(data.write_addr[0] == data.read_addr[1]),
                actual_output.eq(data.write_data[1])
            ]

        with m.Elif(mode == AddressModes.ZEROPAGE_IND.value):
            m.d.comb += [
                Assert(data.post_a == data.pre_a),
                Assert(data.post_pc == data.plus16(data.pre_pc, 2)),
                Assert(data.addresses_read == 2),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                Assert(data.read_addr[1] == data.plus16(data.pre_x, data.read_data[0])),
                input.eq(data.read_data[0])
            ]

            m.d.comb += [
                Assert(data.addresses_written == 2),
                Assert(data.write_addr[0] == data.read_addr[1]),
                actual_output.eq(data.write_data[0])
            ]

        with m.Elif(mode == AddressModes.ABSOLUTE.value):
            m.d.comb += [
                Assert(data.post_a == data.pre_a),
                Assert(data.post_pc == data.plus16(data.pre_pc, 3)),
                Assert(data.addresses_read == 3),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                Assert(data.read_addr[1] == data.plus16(data.pre_pc, 2)),
                Assert(data.read_addr[2] == Cat(data.read_data[0], data.read_data[1])),
                input.eq(data.read_data[2]),
            ]

            m.d.comb += [
                Assert(data.addresses_written == 2),
                Assert(data.write_addr[0] == data.read_addr[2]),
                Assert(data.write_addr[1] == data.read_addr[2]),
                actual_output.eq(data.write_data[1])
            ]

        with m.Elif(mode == AddressModes.ABSOLUTE_X.value):
            m.d.comb += [
                Assert(data.post_a == data.pre_a),
                Assert(data.post_pc == data.plus16(data.pre_pc, 3)),
                Assert(data.addresses_read == 5),
                Assert(data.read_addr[0] == data.plus16(data.pre_pc, 1)),
                Assert(data.read_addr[1] == data.plus16(data.pre_pc, 2)),
                Assert(data.read_addr[3] == data.plus16(Cat(data.read_data[0], data.read_data[1]), data.pre_x)),
                input.eq(data.read_data[2]),
            ]

            m.d.comb += [
                Assert(data.addresses_written == 2),
                Assert(data.write_addr[0] == data.read_addr[3]),
                Assert(data.write_addr[1] == data.read_addr[3]),
                actual_output.eq(data.write_data[1])
            ]

        return (input, actual_output)
