#!/usr/bin/env python3

from peano import Successor as S
from peano import Addition as P
from peano import Multiplication as M
from peano import Equality as Eq
from peano import Variable as V
from peano import from_number as num
from peano import prove

x = V('x')
y = V('y')

# x = 2*1 => x = 2
proof = prove([Eq(x, M(num(2), num(1)))], Eq(x, num(2)))
print(proof)

print('--------')

# x = y * 1 => x = y
proof = prove([Eq(x, M(y, num(1)))], Eq(x, y))
print(proof)

print('--------')

# x = y + 0 => x = y
proof = prove([Eq(x, P(y, num(0)))], Eq(x, y))
print(proof)

print('--------')

# x = y + 1 => x = S(y)
proof = prove([Eq(x, P(y, num(1)))], Eq(x, S(y)))
print(proof)

print('--------')

# x = 9*9 => x = 81 - a bit too much
proof = prove([Eq(x, M(num(9), num(9)))], Eq(x, num(81)))
print(proof)
