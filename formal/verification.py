# verification.py: Formal verification framework for the 6502 CPU.
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

from typing import List, Optional

from nmigen import Signal, Value, Module, Cat, Array
from nmigen.asserts import Assert
from nmigen.hdl.ast import Statement

_N = 7
_V = 6
_B = 4
_D = 3
_I = 2
_Z = 1
_C = 0

class Verification(object):
    def __init__(self):
        pass

    def valid(self, instr: Value) -> Value:
        pass

    def check(self, m: Module, instr: Value, data: 'FormalData'):
        pass

    def flags(self,
              prev: Value,
              N: Value = None,
              V: Value = None,
              B: Value = None,
              D: Value = None,
              I: Value = None,
              Z: Value = None,
              C: Value = None) -> Value:
        if N is None:
            N = prev[_N]
        if V is None:
            V = prev[_V]
        if B is None:
            B = prev[_B]
        if D is None:
            D = prev[_D]
        if I is None:
            I = prev[_I]
        if Z is None:
            Z = prev[_Z]
        if C is None:
            C = prev[_C]

        return Cat(C, Z, I, D, B, 1, V, N)

    def assertFlags(self,
                    m: Module,
                    post_flags: Value,
                    pre_flags: Value,
                    N: Value = None,
                    V: Value = None,
                    B: Value = None,
                    D: Value = None,
                    I: Value = None,
                    Z: Value = None,
                    C: Value = None):
        expectedFlags = Signal(8)
        m.d.comb += expectedFlags.eq(self.flags(pre_flags, N, V, B, D, I, Z, C))
        m.d.comb += [
            Assert(post_flags[_N] == expectedFlags[_N]),
            Assert(post_flags[_V] == expectedFlags[_V]),
            Assert(post_flags[5] == expectedFlags[5]),
            Assert(post_flags[_B] == expectedFlags[_B]),
            Assert(post_flags[_D] == expectedFlags[_D]),
            Assert(post_flags[_I] == expectedFlags[_I]),
            Assert(post_flags[_Z] == expectedFlags[_Z]),
            Assert(post_flags[_C] == expectedFlags[_C]),
        ]


class FormalData(object):
    def __init__(self, verification: Optional[Verification]):
        self.verification = verification
        if verification is None:
            return

        self.snapshot_taken = Signal()

        self.instr = Signal(8)

        self.pre_sr_flags = Signal(8)
        self.pre_a = Signal(8)
        self.pre_x = Signal(8)
        self.pre_y = Signal(8)
        self.pre_sp = Signal(8)
        self.pre_pc = Signal(16)

        self.post_sr_flags = Signal(8)
        self.post_a = Signal(8)
        self.post_x = Signal(8)
        self.post_y = Signal(8)
        self.post_sp = Signal(8)
        self.post_pc = Signal(16)

        self.addresses_written = Signal(3)
        self.write_addr = Array([Signal(16) for _ in range(8)])
        self.write_data = Array([Signal(8) for _ in range(8)])

        self.addresses_read = Signal(3)
        self.read_addr = Array([Signal(16) for _ in range(8)])
        self.read_data = Array([Signal(8) for _ in range(8)])

    def plus16(self, v1: Value, v2: Value) -> Value:
        return (v1 + v2)[:16]

    def plus8(self, v1: Value, v2: Value) -> Value:
        return (v1 + v2)[:8]

    def read(self, m: Module, addr: Value, data: Value):
        if self.verification is None:
            return
        with m.If(self.snapshot_taken):
            with m.If(self.addresses_read != 7):
                m.d.ph1 += self.addresses_read.eq(self.addresses_read + 1)
                m.d.ph1 += self.read_addr[self.addresses_read].eq(addr)
                m.d.ph1 += self.read_data[self.addresses_read].eq(data)

    def write(self, m: Module, addr: Value, data: Value):
        if self.verification is None:
            return
        with m.If(self.snapshot_taken):
            with m.If(self.addresses_read != 7):
                m.d.ph1 += self.addresses_written.eq(self.addresses_written + 1)
                m.d.ph1 += self.write_addr[self.addresses_written].eq(addr)
                m.d.ph1 += self.write_data[self.addresses_written].eq(data)

    def preSnapshot(self, m: Module, instr: Value, sr_flags: Value, a: Value, x: Value, y: Value, sp: Value, pc: Value):
        if self.verification is None:
            return
        m.d.ph1 += self.snapshot_taken.eq(1)
        m.d.ph1 += self.addresses_read.eq(0)
        m.d.ph1 += self.addresses_written.eq(0)
        m.d.ph1 += self.instr.eq(instr)
        m.d.ph1 += self.pre_sr_flags.eq(sr_flags)
        m.d.ph1 += self.pre_a.eq(a)
        m.d.ph1 += self.pre_x.eq(x)
        m.d.ph1 += self.pre_y.eq(y)
        m.d.ph1 += self.pre_sp.eq(sp)
        m.d.ph1 += self.pre_pc.eq(pc)

    def noSnapshot(self, m: Module):
        if self.verification is None:
            return
        m.d.ph1 += self.snapshot_taken.eq(0)

    def postSnapshot(self, m: Module, sr_flags: Value, a: Value, x: Value, y: Value, sp: Value, pc: Value):
        if self.verification is None:
            return
        m.d.comb += self.post_sr_flags.eq(sr_flags)
        m.d.comb += self.post_a.eq(a)
        m.d.comb += self.post_x.eq(x)
        m.d.comb += self.post_y.eq(y)
        m.d.comb += self.post_sp.eq(sp)
        m.d.comb += self.post_pc.eq(pc)
