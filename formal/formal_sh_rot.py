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


from nmigen import Signal, Value, Cat, Module, signed, Mux
from nmigen.hdl.ast import Statement
from nmigen.asserts import Assert
from .verification import FormalData, Verification
from .alu_verification import AluVerification, Alu2Verification
from consts import Flags

def Downto(v: Value, top: int, bottom: int) -> Value:
    """Inclusive slicing.

    Returns an equivalent nMigen
    """
    if bottom > top:
        raise IndexError(
            f"Downto top must be greater than or equal to bottom: {top}, {bottom}"
        )
    return v[bottom : top + 1]


ASL = "000---10"
ROL = "001---10"
LSR = "010---10"
ROR = "011---10"


class Formal(Alu2Verification):
    def __init__(self):
        pass

    def valid(self, instr: Value) -> Value:
        return instr.matches(
            0x0A, 0x06, 0x16, 0x0E, 0x1E,
            0x2A, 0x26, 0x36, 0x2E, 0x3E,
            0x4A, 0x46, 0x56, 0x4E, 0x5E,
            0x6A, 0x66, 0x76, 0x6E, 0x7E
        )

    def check(self, m: Module, instr: Value, data: FormalData):
        input, actual_output = self.common_check(m, instr, data)
        expected_output = Signal(8)

        pre_c = data.pre_sr_flags[Flags.C]
        c = Signal()

        with m.If(instr.matches(ASL)):
            m.d.comb += [
                c.eq(input[7]),
                expected_output[0].eq(0),
                Downto(expected_output, 7, 1).eq(Downto(input, 6, 0))
            ]

        with m.Elif(instr.matches(ROL)):
            m.d.comb += [
                c.eq(input[7]),
                expected_output[0].eq(pre_c),
                Downto(expected_output, 7, 1).eq(Downto(input, 6, 0))
            ]

        with m.Elif(instr.matches(LSR)):
            m.d.comb += [
                c.eq(input[0]),
                expected_output[7].eq(input[7]),
                Downto(expected_output, 6, 0).eq(Downto(input, 7, 1))
            ]

        with m.Elif(instr.matches(ROR)):
            m.d.comb += [
                c.eq(input[0]),
                expected_output[7].eq(pre_c),
                Downto(expected_output, 6, 0).eq(Downto(input, 7, 1)),
            ]
