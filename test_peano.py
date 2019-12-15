#!/usr/bin/env python3

from peano import Successor as S
from peano import Addition as P
from peano import Multiplication as M
from peano import Equality as Eq
from peano import Variable as V
from peano import from_number as num
from peano import prove

x = V('x')
proof = prove([Eq(x, M(num(2), num(1)))], Eq(x, num(2)))
print(proof)
