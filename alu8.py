# alu8.py: 8-bit ALU for the 6502 CPU
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
from typing import List, Dict, Tuple, Optional

from nmigen import Signal, Value, Elaboratable, Module, Cat, Const, Mux
from nmigen import ClockDomain, ClockSignal
from nmigen.build import Platform
from nmigen.cli import main_parser, main_runner
from nmigen.asserts import Assert, Assume
from consts import Flags


class ALU8Func(IntEnum):
    NONE = 0
    LD = 1
    ADC = 2
    SBC = 3
    SUB = 4
    ORA = 5
    AND = 6
    EOR = 7

class ALU8(Elaboratable):
    def __init__(self):
        self.input1 = Signal(8)
        self.input2 = Signal(8)
        self.output = Signal(8)
        self.func = Signal(ALU8Func)

        # NV-BDIZC
        self.sr_flags = Signal(8, reset=0b00100000)
        self._sr_flags = Signal(8)

    def input_ports(self) -> List[Signal]:
        return [self.input1, self.input2, self.func]

    def elaborate(self, platform: Platform) -> Module:
        m = Module()

        m.d.comb += self._sr_flags.eq(self.sr_flags)
        m.d.ph1 += self.sr_flags.eq(self._sr_flags)

        # intermediates
        carry4 = Signal()
        carry7 = Signal()
        carry8 = Signal()
        overflow = Signal()

        with m.Switch(self.func):
            with m.Case(ALU8Func.LD):
                m.d.comb += self.output.eq(self.input2)
                m.d.comb += self._sr_flags[Flags.Z].eq(self.output == 0)
                m.d.comb += self._sr_flags[Flags.N].eq(self.output[7])

            with m.Case(ALU8Func.ADC):
                carry_in = self.sr_flags[Flags.C]

                sum0_3 = Cat(self.output[:4], carry4)
                m.d.comb += sum0_3.eq(self.input1[:4] +
                                      self.input2[:4] + carry_in)
                sum4_6 = Cat(self.output[4:7], carry7)
                m.d.comb += sum4_6.eq(self.input1[4:7] +
                                      self.input2[4:7] + carry4)
                sum7 = Cat(self.output[7], carry8)
                m.d.comb += sum7.eq(self.input1[7] + self.input2[7] + carry7)
                m.d.comb += overflow.eq(carry7 ^ carry8)
                m.d.comb += self._sr_flags[Flags.N].eq(self.output[7])
                m.d.comb += self._sr_flags[Flags.Z].eq(self.output == 0)
                m.d.comb += self._sr_flags[Flags.V].eq(overflow)
                m.d.comb += self._sr_flags[Flags.C].eq(carry8)

            with m.Case(ALU8Func.SBC):
                carry_in = self.sr_flags[Flags.C]

                sum0_6 = Cat(self.output[:7], carry7)
                m.d.comb += sum0_6.eq(self.input1[:7] +
                                      ~self.input2[:7] + ~carry_in)
                sum7 = Cat(self.output[7], carry8)
                m.d.comb += sum7.eq(self.input1[7] + ~self.input2[7] + carry7)
                m.d.comb += overflow.eq(carry7 ^ carry8)
                m.d.comb += self._sr_flags[Flags.N].eq(self.output[7])
                m.d.comb += self._sr_flags[Flags.Z].eq(self.output == 0)
                m.d.comb += self._sr_flags[Flags.V].eq(overflow)
                m.d.comb += self._sr_flags[Flags.C].eq(~carry8)

            with m.Case(ALU8Func.SUB):
                sum0_6 = Cat(self.output[:7], carry7)
                m.d.comb += sum0_6.eq(self.input1[:7] + ~self.input2[:7] + 1)
                sum7 = Cat(self.output[7], carry8)
                m.d.comb += sum7.eq(self.input1[7] + ~self.input2[7] + carry7)
                m.d.comb += overflow.eq(carry7 ^ carry8)
                m.d.comb += self._sr_flags[Flags.N].eq(self.output[7])
                m.d.comb += self._sr_flags[Flags.Z].eq(self.output == 0)
                m.d.comb += self._sr_flags[Flags.C].eq(~carry8)

            with m.Case(ALU8Func.ORA):
                m.d.comb += self.output.eq(self.input1 | self.input2)
                m.d.comb += self._sr_flags[Flags.N].eq(self.output[7])
                m.d.comb += self._sr_flags[Flags.Z].eq(self.output == 0)

            with m.Case(ALU8Func.AND):
                m.d.comb += self.output.eq(self.input1 & self.input2)
                m.d.comb += self._sr_flags[Flags.N].eq(self.output[7])
                m.d.comb += self._sr_flags[Flags.Z].eq(self.output == 0)

            with m.Case(ALU8Func.EOR):
                m.d.comb += self.output.eq(self.input1 ^ self.input2)
                m.d.comb += self._sr_flags[Flags.N].eq(self.output[7])
                m.d.comb += self._sr_flags[Flags.Z].eq(self.output == 0)

        return m


if __name__ == "__main__":
    parser = main_parser()
    args = parser.parse_args()

    m = Module()
    m.submodules.alu = alu = ALU8()
    m.domains.ph1 = ph1 = ClockDomain("ph1")

    rst = Signal()
    ph1clk = ClockSignal("ph1")
    ph1.rst = rst

    carry_in = Signal()
    sum9 = Signal(9)
    sum8 = Signal(8)
    sum5 = Signal(5)

    # NV-BDIZC
    m.d.comb += Assert(alu._sr_flags[5] == 1)
    m.d.comb += Assert(alu._sr_flags[Flags.B] == 0)
    m.d.comb += Assert(alu._sr_flags[Flags.D] == 0)
    m.d.comb += Assert(alu._sr_flags[Flags.I] == 0)

    with m.Switch(alu.func):
        with m.Case(ALU8Func.ADC):
            # sumN = input1[:N] + input2[:N] (so sumN[N-1] is the carry bit)
            m.d.comb += carry_in.eq(alu.sr_flags[Flags.C])
            h = sum5[4]
            n = sum9[7]
            c = sum9[8]
            z = (sum9[:8] == 0)
            v = (sum8[7] ^ c)
            m.d.comb += [
                sum9.eq(alu.input1 + alu.input2 + carry_in),
                sum8.eq(alu.input1[:7] + alu.input2[:7] + carry_in),
                sum5.eq(alu.input1[:4] + alu.input2[:4] + carry_in),
                Assert(alu.output == sum9[:8]),
                Assert(alu._sr_flags[Flags.N] == n),
                Assert(alu._sr_flags[Flags.Z] == z),
                Assert(alu._sr_flags[Flags.V] == v),
                Assert(alu._sr_flags[Flags.C] == c),
                Assert(alu._sr_flags[Flags.I] == alu.sr_flags[Flags.I]),
            ]
        with m.Case(ALU8Func.SBC):
            m.d.comb += carry_in.eq(alu.sr_flags[Flags.C])
            n = sum9[7]
            c = ~sum9[8]
            z = (sum9[:8] == 0)
            v = (sum8[7] ^ sum9[8])
            m.d.comb += [
                sum9.eq(alu.input1 + ~alu.input2 + ~carry_in),
                sum8.eq(alu.input1[:7] + ~alu.input2[:7] + ~carry_in),
                Assert(sum9[:8] == (
                    alu.input1 - alu.input2 - carry_in)[:8]),
                Assert(alu.output == sum9[:8]),
                Assert(alu._sr_flags[Flags.N] == n),
                Assert(alu._sr_flags[Flags.Z] == z),
                Assert(alu._sr_flags[Flags.V] == v),
                Assert(alu._sr_flags[Flags.C] == c),
                Assert(alu._sr_flags[Flags.I] == alu.sr_flags[Flags.I]),
            ]

    main_runner(parser, args, m, ports=alu.input_ports() + [ph1clk, rst])
