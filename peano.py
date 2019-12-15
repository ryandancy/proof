#!/usr/bin/env python3

"""
We use the following (not super the mathematical way but ok):

EQUALITY AXIOMS.
S. Substitution property: forall x, y, if x = y and P(x), then P(y).  # stated meh-ly
R. forall x, x = x.
SY. forall x, y, x = y => y = x.
T. forall x, y, z, x = y and y = z => x = z.

THE PEANO AXIOMS.
P1. 0 in N.
P2. forall n in N, S(n) in N.
P3. forall n, m in N, n = m <=> S(n) = S(m).
P4. forall n in N, S(n) != 0.
P5. ((0 in K) and (forall n in N, (n in K => S(n) in K))) => (forall n in N, n in K). # induction

DEFINITION OF ADDITION. Forall a, b in N,
A1. a + 0 = a.
A2. a + S(b) = S(a + b).

DEFINITION OF MULTIPLICATION. Forall a, b in N,
M1. a * 0 = 0.
M2. a * S(b) = a + (a * b).
"""


# Types of natural-number objects: Zero, Successor, Variable, Addition, Multiplication
# Each have an equal_exprs() method which returns a list of things trivially equal to it
# If b in a.equal_exprs(), then we must have a in b.equal_exprs().


class Zero:
  """The object '0', the existence of which is asserted in P1."""
  
  def equal_exprs(self):
    return [] # 0 is not simplifiable.
  
  def __str__(self):
    return '0'
  
  def __eq__(self, o):
    return isinstance(o, Zero) # all zeros are equal

# For convenience, we have a single zero
ZERO = Zero()


class Successor:
  """The successor function S(n) with the properties asserted in P2, P3, and P4."""
  
  def __init__(self, val):
    self.val = val
  
  def equal_exprs(self):
    exprs = []
    
    # A2: S(a + b) = a + S(b)
    if isinstance(self.val, Addition):
      exprs.append(Addition(a, Successor(b)))
    
    return exprs
  
  def __str__(self):
    return f'S({self.val})'
  
  def __eq__(self, o):
    return self.val == o.val # by P3


def from_number(a):
  """A convenience function to convert a Python integer into successor form."""
  if a < 0:
    raise ValueError('Only natural numbers can be represented.')
  if a == 0:
    return ZERO
  return Successor(from_number(a - 1))


class Variable:
  """A variable holding a natural number, defined by its unique symbol."""
  
  def __init__(self, symbol):
    self.symbol = symbol
  
  def equal_exprs(self):
    return [] # a lone variable cannot be simplified
  
  def __str__(self):
    return self.symbol
  
  def __eq__(self, o):
    return self.symbol == o.symbol # obeys equality axioms


class Addition:
  """The expression a + b."""
  
  def __init__(self, a, b):
    self.a, self.b = a, b
  
  def equal_exprs(self):
    exprs = []
    
    # A1: a + 0 = a
    if self.b == ZERO:
      exprs.append(a)
    
    # A2: a + S(b) = S(a + b)
    if isinstance(self.b, Successor):
      exprs.append(Successor(Addition(self.a, self.b.val)))
    
    # M2: a + (a * b) = a * S(b)
    if isinstance(self.b, Multiplication) and self.a == self.b.a:
      exprs.append(Multiplication(a, Successor(b)))
    
    return exprs
  
  def __str__(self):
    return f'({self.a} + {self.b})'
  
  def __eq__(self, o):
    # TODO consult some equality list to determine this
    return isinstance(o, Addition) and self.a == o.a and self.b == o.b


class Multiplication:
  """The expression a * b."""
  
  def __init__(self, a, b):
    self.a, self.b = a, b
  
  def equal_exprs(self):
    exprs = []
    
    # M1: a * 0 = 0
    if self.b == ZERO:
      exprs.append(ZERO)
    
    # M2: a * S(b) = a + (a * b)
    if isinstance(b, Successor):
      exprs.append(Addition(a, Multiplication(a, b)))
    
    return exprs
  
  def __str__(self):
    return f'({self.a} * {self.b})'
  
  def __eq__(self, o):
    # TODO consult a list
    return isinstance(o, Multiplication) and self.a == o.a and self.b == o.b
