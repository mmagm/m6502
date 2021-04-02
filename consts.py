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
    IMMEDIATE = 0  # immediate
    ZEROPAGE = 1   # zeropage
    ZEROPAGE_X = 2 # zeropage,X
    ABSOLUTE = 3   # absolute
    ABSOLUTE_X = 4 # absolute,X
    ABSOLUTE_Y = 5 # absolute,Y
    # INDIRECT JMP $(HHLL)
    INDIRECT_X = 6 # (indirect,X)
    INDIRECT_Y = 7 # (indirect),Y


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
