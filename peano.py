#!/usr/bin/env python3

"""
We use the following (not super the mathematical way but ok):

EQUALITY AXIOMS.
S. Substitution property: forall x, y, if x = y and P(x), then P(y).  # stated meh-ly
R. forall x, x = x.
SY. forall x, y, x = y => y = x.
T. forall x, y, z, x = y and y = z => x = z.

THE PEANO AXIOMS.
P1. exists 0 in N.
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

import itertools
from typing import Sequence, Tuple

# No good very bad prototype of an automated theorem prover with the Peano axioms
# Types of natural-number objects: Zero, Successor, Variable, Addition, Multiplication
# Each have an equal_exprs() method which returns a list of (expr trivially equal, [(equality step, str justification), ...])
# If b is in a.equal_exprs()'s first elements, then we must have a in b.equal_exprs()'s first elements.

# I really should have used type hints, shouldn't I have?

# Here's some justification string constants so we can change them up here.
S = 'substitution'
R = 'reflexivity of equality'
SY = 'symmetry of equality'
T = 'transitivity of equality'
P1 = 'P1' # 0 in N
P2 = 'P2' # N is closed under S
P3 = 'P3' # S is injective
P4 = 'P4' # S(n) != 0
P5 = 'P5' # induction
A1 = 'A1' # a + 0 = a
A2 = 'A2' # a + S(b) = S(a + b)
M1 = 'M1' # a * 0 = 0
M2 = 'M2' # a * S(b) = a + (a * b)

class Zero:
  """The object '0', the existence of which is asserted in P1."""
  
  def equal_exprs(self):
    return [] # 0 is not simplifiable.
  
  def __str__(self):
    return '0'
  
  def __eq__(self, o):
    return isinstance(o, Zero) # all zeros are equal
  
  def __hash__(self):
    return 53 # they're all equal and this is prime

# For convenience, we have a single zero
ZERO = Zero()


def sub_equal_exprs(expr, sub_exprs, convert_sub_expr_to_expr):
  """A utility function for generating all the substitution steps to convert a sub-expression (like n in S(n)) to a top-level expression."""
  additional_exprs = []
  for sub_expr, steps in sub_exprs:
    new_expr = convert_sub_expr_to_expr(sub_expr)
    additional_exprs.append((new_expr, steps + [(Equality(expr, new_expr), S)]))
  return additional_exprs


class Successor:
  """The successor function S(n) with the properties asserted in P2, P3, and P4."""
  
  def __init__(self, val):
    self.val = val
  
  def equal_exprs(self):
    exprs = []
    
    # A2: S(a + b) = a + S(b)
    if isinstance(self.val, Addition):
      new_expr = Addition(self.val.a, Successor(self.val.b))
      exprs.append((new_expr, [(Equality(self, new_expr), A2)]))
    
    # sub-exprs
    exprs += sub_equal_exprs(self, self.val.equal_exprs(), Successor)
    
    return exprs
  
  def __str__(self):
    return f'S({self.val})'
  
  def __eq__(self, o):
    return isinstance(o, Successor) and self.val == o.val # by P3
  
  def __hash__(self):
    return 7 * hash((self.val,))


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
    return isinstance(o, Variable) and self.symbol == o.symbol # obeys equality axioms
  
  def __hash__(self):
    return 87 * hash((self.symbol,))


class Addition:
  """The expression a + b."""
  
  def __init__(self, a, b):
    self.a, self.b = a, b
  
  def equal_exprs(self):
    exprs = []
    
    # A1: a + 0 = a
    if self.b == ZERO:
      exprs.append((self.a, [(Equality(self, self.a), A1)]))
    
    # A2: a + S(b) = S(a + b)
    if isinstance(self.b, Successor):
      new_expr = Successor(Addition(self.a, self.b.val))
      exprs.append((new_expr, [(Equality(self, new_expr), A2)]))
    
    # M2: a + (a * b) = a * S(b)
    if isinstance(self.b, Multiplication) and self.a == self.b.a:
      new_expr = Multiplication(self.a, Successor(self.b.b))
      exprs.append((new_expr, [(Equality(self, new_expr), M2)]))
    
    # sub-exprs for left and right
    exprs += sub_equal_exprs(self, self.a.equal_exprs(), lambda sub_expr: Addition(sub_expr, self.b))
    exprs += sub_equal_exprs(self, self.b.equal_exprs(), lambda sub_expr: Addition(self.a, sub_expr))
    
    return exprs
  
  def __str__(self):
    return f'({self.a} + {self.b})'
  
  def __eq__(self, o):
    return isinstance(o, Addition) and self.a == o.a and self.b == o.b
  
  def __hash__(self):
    return 13 * hash((self.a, self.b))


class Multiplication:
  """The expression a * b."""
  
  def __init__(self, a, b):
    self.a, self.b = a, b
  
  def equal_exprs(self):
    exprs = []
    
    # M1: a * 0 = 0
    if self.b == ZERO:
      exprs.append((ZERO, [(Equality(self, ZERO), M1)]))
    
    # M2: a * S(b) = a + (a * b)
    if isinstance(self.b, Successor):
      new_expr = Addition(self.a, Multiplication(self.a, self.b.val))
      exprs.append((new_expr, [(Equality(self, new_expr), M2)]))
    
    # sub-exprs for left and right
    exprs += sub_equal_exprs(self, self.a.equal_exprs(), lambda sub_expr: Multiplication(sub_expr, self.b))
    exprs += sub_equal_exprs(self, self.b.equal_exprs(), lambda sub_expr: Multiplication(self.a, sub_expr))
    
    return exprs
  
  def __str__(self):
    return f'({self.a} * {self.b})'
  
  def __eq__(self, o):
    return isinstance(o, Multiplication) and self.a == o.a and self.b == o.b
  
  def __hash__(self):
    return 17 * hash((self.a, self.b))


# Will have to be generalized to a "Known" for general things that are known if we ever want to include stuff like
# divisibility or whatever, but this is good enough for 1+1=2, etc
class Equality:
  """An assertion that all of the items are equal."""
  
  def __init__(self, *items):
    self.items = list(items)
    self.representative = items[0] # so we don't have big long a = b = c = ...
  
  def add_item(self, item):
    self.items.append(item)
  
  def __str__(self):
    return ' = '.join(map(str, self.items))
  
  def __eq__(self, o):
    """Treated as equivalence."""
    if not isinstance(o, Equality):
      return False
    
    # obeys SY and R
    return set(self.items) == set(o.items)
  
  def __hash__(self):
    return 19 * hash(set(self.items))


class Proof:
  """A set of steps, each following from the next with justification, following an argument from hypothesis to conclusion."""
  
  def __init__(self, hypotheses, conclusion):
    self.hypothesis_str = ' and '.join(map(str, hypotheses))
    self.conclusion = conclusion
    self.steps = [] # Each step is (Equality, str justification)
  
  def add_step(self, equality, justification):
    self.steps.append((equality, justification))
  
  def __str__(self):
    proof = f'Proposition. ({self.hypothesis_str}) => ({self.conclusion}).\nSuppose {self.hypothesis_str}.\n'
    for i, step in enumerate(self.steps):
      proof += f'{i+1}. {step[0]} (by {step[1]})\n'
    proof += f'Therefore {self.conclusion}. QED.'
    return proof


def prove(hypotheses: Sequence[Equality], conclusion: Equality) -> Proof:
  # the world's least efficient symbol manipulation routine
  # we're just going to keep stock of all the equalities and give up when the size no longer changes
  # this will run forever on any more complicated axiomatic system, probably
  # this is a breadth-first search, essentially
  
  proof = Proof(hypotheses, conclusion)
  
  if conclusion in hypotheses:
    return proof # well that was easy
  
  equalities = list(hypotheses)
  explore_queue = [(expr, hypot) for hypot in hypotheses for expr in hypot.items] # list of (expr, equality)
  
  # just fill in all the equalities we can, what could go wrong
  while explore_queue:
    member, eq = explore_queue.pop(0) # inefficient but whatever
    
    exprs = member.equal_exprs()
    
    for expr, steps in exprs:
      if expr not in eq.items and (expr, eq) not in explore_queue:
        eq.items.append(expr)
        explore_queue.append((expr, eq))
        
        for equality, justification in steps:
          proof.add_step(equality, justification) # BAD BAD BAD
        
        # transitivity
        if member != eq.representative:
          proof.add_step(Equality(eq.representative, expr), T) # proactive transitivity is probably bad
        
        if set(conclusion.items).issubset(eq.items):
          # just to make it look nicer, add another transitivity step
          if conclusion.items != [eq.representative, expr] and conclusion.items != [expr, eq.representative]:
            proof.add_step(conclusion, T)
          return proof
  
  return None # we've looked everywhere and found nothing
