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


class AddressModes(IntEnum):
    """Decoding of bits 4, 3, and 2 for instructions."""
    INDIRECT_X = 0 # (indirect,X)
    ZEROPAGE = 1   # zeropage
    IMMEDIATE = 2  # immediate
    ABSOLUTE = 3   # absolute
    INDIRECT_Y = 4 # (indirect),Y
    ZEROPAGE_IND = 5 # zeropage,X
    ABSOLUTE_Y = 6 # absolute,Y
    ABSOLUTE_X = 7 # absolute,X


class Flags(IntEnum):
    """Flag positions."""
    N = 7 # Negative
    V = 6 # Overflow
    _ = 5 # ignored
    B = 4 # Break
    D = 3 # Decimal (use BCD for arithmetics)
    I = 2 # Interrupt (IRQ disable)
    Z = 1 # Zero
    C = 0 # Carry
