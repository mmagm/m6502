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

from nmigen import Signal, Value, Module, Cat, Mux
from consts import Flags
from .alu_verification import AluVerification


class Formal(AluVerification):
    def __init__(self):
        super().__init__()

    def valid(self, instr: Value) -> Value:
        return instr.matches("111---01")

    def check(self, m: Module):
        input1, input2, actual_output, size = self.common_check(m)

        carry_in = Signal()
        m.d.comb += carry_in.eq(self.data.pre_sr_flags[Flags.C])

        decimal_mode = self.data.pre_sr_flags[Flags.D]

        v = Signal()
        n = Signal()
        z = Signal()
        c = Signal()

        res_lo = Signal(5)
        res_hi = Signal(5)

        result = Cat(res_lo[:4], res_hi)

        out = Signal(8)

        half_carry = Signal()
        carry_out = Signal()

        with m.If(decimal_mode):
            dec_hc = Signal()
            dec_co = Signal()

            adj_lo = Signal(4)
            adj_hi = Signal(4)

            m.d.comb += [
                dec_hc.eq(res_lo[1:4] >= 5),
                half_carry.eq(res_lo[4] | dec_hc),
                dec_co.eq(res_hi[1:4] >= 5),
                carry_out.eq(result[8] | dec_co),
                res_lo.eq(input1[:4] + ~input2[:4] + carry_in),
                res_hi.eq(input1[4:8] + ~input2[4:8] + half_carry),
                v.eq(input1[7] ^ ~input2[7] ^ carry_out ^ result[7]),
                n.eq(result[7]),
                z.eq(result[:8] == 0),
                c.eq(carry_out),
                adj_lo.eq(Mux(~half_carry, 10, 0)),
                adj_hi.eq(Mux(~carry_out, 10, 0)),
                out[:4].eq(result[:4] + adj_lo),
                out[4:8].eq(result[4:8] + adj_hi),
            ]

        with m.Else():
            m.d.comb += [
                half_carry.eq(res_lo[4]),
                carry_out.eq(result[8]),
                res_lo.eq(input1[:4] + ~input2[:4] + carry_in),
                res_hi.eq(input1[4:8] + ~input2[4:8] + half_carry),
                v.eq(input1[7] ^ ~input2[7] ^ carry_out ^ result[7]),
                n.eq(result[7]),
                z.eq(result[:8] == 0),
                c.eq(carry_out),
                out[:4].eq(result[:4]),
                out[4:8].eq(result[4:8]),
            ]

        self.assert_registers(m, A=out, PC=self.data.pre_pc+size)
        self.assertFlags(m, Z=z, N=n, V=v, C=c)
