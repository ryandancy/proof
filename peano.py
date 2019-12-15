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


# Types of natural-number objects: Zero, Successor, Variable, Addition, Multiplication
# Each have an equal_exprs() method which returns a list of (expr trivially equal, justification str)
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
      exprs.append((Addition(self.val.a, Successor(self.val.b)), A2))
    
    # sub-exprs
    exprs += map(lambda sub_expr: (Successor(sub_expr[0]), sub_expr[1]), self.val.equal_exprs())
    
    return exprs
  
  def __str__(self):
    return f'S({self.val})'
  
  def __eq__(self, o):
    return isinstance(o, Successor) and self.val == o.val # by P3


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


class Addition:
  """The expression a + b."""
  
  def __init__(self, a, b):
    self.a, self.b = a, b
  
  def equal_exprs(self):
    exprs = []
    
    # A1: a + 0 = a
    if self.b == ZERO:
      exprs.append((self.a, A1))
    
    # A2: a + S(b) = S(a + b)
    if isinstance(self.b, Successor):
      exprs.append((Successor(Addition(self.a, self.b.val)), A2))
    
    # M2: a + (a * b) = a * S(b)
    if isinstance(self.b, Multiplication) and self.a == self.b.a:
      exprs.append((Multiplication(self.a, Successor(self.b.b)), M2))
    
    # sub-exprs for left and right
    exprs += map(lambda sub_expr: (Addition(sub_expr[0], self.b), sub_expr[1]), self.a.equal_exprs())
    exprs += map(lambda sub_expr: (Addition(self.a, sub_expr[0]), sub_expr[1]), self.b.equal_exprs())
    
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
      exprs.append((ZERO, M1))
    
    # M2: a * S(b) = a + (a * b)
    if isinstance(self.b, Successor):
      exprs.append((Addition(self.a, Multiplication(self.a, self.b.val)), M2))
    
    # sub-exprs for left and right
    exprs += map(lambda sub_expr: (Multiplication(sub_expr[0], self.b), sub_expr[1]), self.a.equal_exprs())
    exprs += map(lambda sub_expr: (Multiplication(self.a, sub_expr[0]), sub_expr[1]), self.b.equal_exprs())
    
    return exprs
  
  def __str__(self):
    return f'({self.a} * {self.b})'
  
  def __eq__(self, o):
    # TODO consult a list
    return isinstance(o, Multiplication) and self.a == o.a and self.b == o.b


# Will have to be generalized to a "Known" for general things that are known if we ever want to include stuff like
# divisibility or whatever, but this is good enough for 1+1=2, etc
class Equality:
  """An assertion that a = b."""
  
  def __init__(self, a, b):
    self.a, self.b = a, b
  
  def __str__(self):
    return f'{self.a} = {self.b}'
  
  def __eq__(self, o):
    """Treated as equivalence."""
    if not isinstance(o, Equality):
      return False
    
    # (a = b) <=> (a = b) - sort of R
    if self.a == o.a and self.b == o.b:
      return True
    
    # (a = b) <=> (b = a) - SY
    if self.a == o.b and self.b == o.a:
      return True
    
    return False


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
    proof += f'Therefore {self.conclusion}.'
    return proof


def prove(hypotheses, conclusion) -> Proof:
  # the world's least efficient symbol manipulation routine
  # we're just going to keep stock of all the equalities and give up when the size no longer changes
  # this will run forever on any more complicated axiomatic system, probably
  # this is like O(n!) or something
  
  proof = Proof(hypotheses, conclusion)
  
  if conclusion in hypotheses:
    return proof # well that was easy
  
  equalities = list(hypotheses)
  
  while True:
    adding_equalities = []
    
    # generate all the equalities we can - O(who the heck knows at this point)
    for eq in equalities:
      for side in (eq.a, eq.b):
        exprs = side.equal_exprs()
        
        for expr, justification in exprs:
          new_eq = Equality(side, expr)
          
          if new_eq not in equalities and new_eq not in adding_equalities:
            adding_equalities.append(new_eq)
            proof.add_step(new_eq, justification) # this is a BAD IDEA with a capital BAD
            
            if new_eq == conclusion:
              return proof
    
    if not adding_equalities:
      # we've done a complete search and turned up nothing - we need something fancier like induction
      return None
    
    equalities += adding_equalities
    
    # now let's apply transitivity in an O(n^2) step for funsies - should generalize this for doing it with others
    trans_equalities = [] # trans rights!
    
    for eq1, eq2 in itertools.combinations(equalities, 2):
      new_eq = None
      
      if eq1.a == eq2.a:
        new_eq = Equality(eq1.b, eq2.b)
      elif eq1.a == eq2.b:
        new_eq = Equality(eq1.b, eq2.a)
      elif eq1.b == eq2.a:
        new_eq = Equality(eq1.a, eq2.b)
      elif eq1.b == eq2.b:
        new_eq = Equality(eq1.a, eq2.a)
      
      if new_eq and new_eq not in equalities and new_eq not in trans_equalities:
        trans_equalities.append(new_eq)
        proof.add_step(new_eq, T) # NO GOOD VERY BAD
        
        if new_eq == conclusion:
          return proof
    
    equalities += trans_equalities
