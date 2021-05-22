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

from nmigen import Signal, Value, Module, Cat, Array, unsigned, Mux
from nmigen.asserts import Assert
from nmigen.hdl.ast import Statement
from nmigen.hdl.rec import Record, Layout
from consts import Flags


class CycleSignals(Record):
    def __init__(self, name: str = None):
        super().__init__(Layout([
            ("address", unsigned(16)),
            ("data_in", unsigned(8)),
            ("data_out", unsigned(8)),
            ("rw", unsigned(1)),
            ("nmi", unsigned(1)),
            ("irq", unsigned(1)),
        ]), name=name)


class Verification(object):
    def __init__(self):
        self.want_cycles = Signal(4, name="want_cycles")
        self.want_a = Signal(8, name="want_a")
        self.want_x = Signal(8, name="want_x")
        self.want_y = Signal(8, name="want_y")
        self.want_pc = Signal(16, name="want_pc")
        self.want_sp = Signal(8, name="want_sp")
        self.want_sr_flags = Signal(8, name="want_sr_flags")
        self.want_signals = Array([CycleSignals(name=f"want_{i}_") for i in range(16)])

    def valid(self, instr: Value) -> Value:
        pass

    def check(self, m: Module):
        pass

    def verify(self, m: Module, instr: Value, data: 'FormalData'):
        self.data = data
        self.instr = instr
        self.check(m)

    def assert_cycles(self, m: Module, cycles: int):
        m.d.comb += self.want_cycles.eq(cycles)
        m.d.comb += Assert(self.data.cycle == self.want_cycles)

    def assert_cycle_signals(self, m: Module, cycle: int,
                             address: Value = None, rw: int = 0) -> Value:

        want = self.want_signals[cycle]
        got = self.data.cycle_records[cycle]

        m.d.comb += [
            want.rw.eq(rw),
            want.address.eq(address),
            Assert(want.rw == got.rw),
            Assert(want.address == got.address)
        ]

        return got.data_in if rw == 1 else got.data_out

    def assert_registers(self, m: Module, A: Value = None, X: Value = None,
                         Y: Value = None, SP: Value = None, PC: Value = None):
        if A is not None:
            m.d.comb += self.want_a.eq(A[:8])
        else:
            m.d.comb += self.want_a.eq(self.data.pre_a)
        if X is not None:
            m.d.comb += self.want_x.eq(X[:8])
        else:
            m.d.comb += self.want_x.eq(self.data.pre_x)
        if Y is not None:
            m.d.comb += self.want_y.eq(Y[:8])
        else:
            m.d.comb += self.want_y.eq(self.data.pre_y)
        if SP is not None:
            m.d.comb += self.want_sp.eq(SP[:8])
        else:
            m.d.comb += self.want_sp.eq(self.data.pre_sp)
        if PC is not None:
            m.d.comb += self.want_pc.eq(PC[:16])
        else:
            m.d.comb += self.want_pc.eq(self.data.pre_pc)

        m.d.comb += Assert(self.data.post_a == self.want_a)
        m.d.comb += Assert(self.data.post_x == self.want_x)
        m.d.comb += Assert(self.data.post_y == self.want_y)
        m.d.comb += Assert(self.data.post_sp == self.want_sp)
        m.d.comb += Assert(self.data.post_pc == self.want_pc)

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
            N = prev[Flags.N]
        if V is None:
            V = prev[Flags.V]
        if B is None:
            B = prev[Flags.B]
        if D is None:
            D = prev[Flags.D]
        if I is None:
            I = prev[Flags.I]
        if Z is None:
            Z = prev[Flags.Z]
        if C is None:
            C = prev[Flags.C]

        return Cat(C, Z, I, D, B, 1, V, N)

    def assertFlags(self,
                    m: Module,
                    N: Value = None,
                    V: Value = None,
                    B: Value = None,
                    D: Value = None,
                    I: Value = None,
                    Z: Value = None,
                    C: Value = None):
        expectedFlags = Signal(8)
        m.d.comb += expectedFlags.eq(self.flags(self.data.pre_sr_flags, N, V, B, D, I, Z, C))
        m.d.comb += [
            Assert(self.data.post_sr_flags[Flags.N] == expectedFlags[Flags.N]),
            Assert(self.data.post_sr_flags[Flags.V] == expectedFlags[Flags.V]),
            # Assert(self.data.post_sr_flags[Flags._] == expectedFlags[Flags._]),
            Assert(self.data.post_sr_flags[Flags.B] == expectedFlags[Flags.B]),
            Assert(self.data.post_sr_flags[Flags.D] == expectedFlags[Flags.D]),
            Assert(self.data.post_sr_flags[Flags.I] == expectedFlags[Flags.I]),
            Assert(self.data.post_sr_flags[Flags.Z] == expectedFlags[Flags.Z]),
            Assert(self.data.post_sr_flags[Flags.C] == expectedFlags[Flags.C]),
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

        self.max_cycles = 16

        self.cycle = Signal(range(self.max_cycles), name="record_cycle")
        self.cycle_records = Array([CycleSignals(name=f"record{i}")
                                    for i in range(self.max_cycles)])

    def snapshot_signals(self, m: Module, addr: Value, din: Value, dout: Value,
                         rw: Value, irq: Value, nmi: Value) -> List[Statement]:
        s = self.cycle_records[self.cycle]

        return [
            s.address.eq(addr),
            s.data_in.eq(din),
            s.data_out.eq(dout),
            s.rw.eq(rw),
            s.irq.eq(irq),
            s.nmi.eq(nmi),
            self.cycle.eq(self.cycle + 1),
        ]

    def preSnapshot(self, m: Module, instr: Value, sr_flags: Value, a: Value, x: Value, y: Value, sp: Value, pc: Value) -> List[Statement]:
        return [
            self.snapshot_taken.eq(1),
            self.instr.eq(instr),
            self.pre_sr_flags.eq(sr_flags),
            self.pre_a.eq(a),
            self.pre_x.eq(x),
            self.pre_y.eq(y),
            self.pre_sp.eq(sp),
            self.pre_pc.eq(pc),
            self.cycle.eq(1)
        ]

    def noSnapshot(self, m: Module) -> Statement:
        return self.snapshot_taken.eq(0)

    def postSnapshot(self, m: Module, sr_flags: Value, a: Value, x: Value, y: Value, sp: Value, pc: Value) -> List[Statement]:
        return [
            self.post_sr_flags.eq(sr_flags),
            self.post_a.eq(a),
            self.post_x.eq(x),
            self.post_y.eq(y),
            self.post_sp.eq(sp),
            self.post_pc.eq(pc)
        ]
