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

import copy
import itertools
from typing import Sequence, List, Tuple, Set, Dict

# No good very bad prototype of an automated theorem prover with the Peano axioms
# Types of natural-number objects: Zero, Successor, Variable, Addition, Multiplication
# Each have an equal_exprs() method which returns a list of (expr trivially equal, [(equality step, str justification), ...])
# Each also have a children() method which returns a tuple of natural-number objects inside them
# and a set_child(n, v) method which sets the nth child to v.
# TODO we don't give a -> a + 0 in equal_exprs(), so this isn't technically complete - how to do this without running forever?
# TODO use children() to do the substitution stuff more elegantly

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
ASSUMPTION = 'assumption'


class Natural:
  """A base class for the natural number representations."""
  
  def equal_exprs(self):
    return []
  
  def children(self):
    return []
  
  def set_child(self, n, value):
    raise NotImplementedError


class Zero(Natural):
  """The object '0', the existence of which is asserted in P1."""
  
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


class Successor(Natural):
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
  
  def children(self):
    return (self.val,)
  
  def set_child(self, n, value: Natural):
    if n != 0:
      raise IndexError
    self.val = value
  
  def __str__(self):
    return f'S({self.val})'
  
  def __eq__(self, o):
    return isinstance(o, Successor) and self.val == o.val # by P3
  
  def __hash__(self):
    return 7 * hash(self.val)


def from_number(a):
  """A convenience function to convert a Python integer into successor form."""
  if a < 0:
    raise ValueError('Only natural numbers can be represented.')
  if a == 0:
    return ZERO
  return Successor(from_number(a - 1))


class Variable(Natural):
  """A variable holding a natural number, defined by its unique symbol."""
  
  def __init__(self, symbol):
    self.symbol = symbol
  
  def __str__(self):
    return self.symbol
  
  def __eq__(self, o):
    return isinstance(o, Variable) and self.symbol == o.symbol # obeys equality axioms
  
  def __hash__(self):
    return 87 * hash((self.symbol,))


def find_variables_in_natural(natural: Natural) -> Set[Variable]:
  """Get a set of all the distinct variables in the natural and its children."""
  
  variables = {var for child in natural.children() for var in find_variables_in_natural(child)}
  if isinstance(natural, Variable):
    variables.add(natural)
  
  return variables

def find_variables(*equalities) -> Set[Variable]:
  """Get a list of all the distinct variables in the equalities."""
  return {var for equality in equalities for item in equality.items for var in find_variables_in_natural(item)}

def substitute_variable_in_natural(variable: Variable, value: Natural, natural: Natural) -> Natural:
  """Deep-copy the natural, but with variable substituted for value."""
  
  # try to substitute if this is a variable
  if natural == variable:
    return copy.deepcopy(value)
  
  # shallow copy and substitute all the children
  new = copy.copy(natural)
  for i, child in enumerate(new.children()):
    new.set_child(i, substitute_variable_in_natural(variable, value, child))
  
  return new

def substitute_variable(variable: Variable, value: Natural, *equalities):
  """Deep-copy the equalities, but with variable substituted for value."""
  return [Equality(*[substitute_variable_in_natural(variable, value, item) for item in equality.items]) for equality in equalities]


class Addition(Natural):
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
  
  def children(self):
    return self.a, self.b
  
  def set_child(self, n, value: Natural):
    if n == 0:
      self.a = value
    elif n == 1:
      self.b = value
    else:
      raise IndexError
  
  def __str__(self):
    return f'({self.a} + {self.b})'
  
  def __eq__(self, o):
    return isinstance(o, Addition) and self.a == o.a and self.b == o.b
  
  def __hash__(self):
    return 13 * hash((self.a, self.b))


class Multiplication(Natural):
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
  
  def children(self):
    return self.a, self.b
  
  def set_child(self, n, value: Natural):
    if n == 0:
      self.a = value
    elif n == 1:
      self.b = value
    else:
      raise IndexError
  
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
    self.item_set = set(items) # for efficiency
    self.representative = items[0] # so we don't have big long a = b = c = ...
  
  def add_item(self, item):
    if item not in self.item_set: # make sure they don't go out of sync
      self.items.append(item)
      self.item_set.add(item)
  
  def __str__(self):
    return ' = '.join(map(str, self.items))
  
  def __eq__(self, o):
    """Treated as equivalence."""
    if not isinstance(o, Equality):
      return False
    
    # obeys SY and R
    return self.item_set == o.item_set
  
  def __hash__(self):
    hsh = 19
    for item in self.item_set:
      hsh *= hash(item)
    return hsh


# TODO have like a general implication with a real quantifier system rather than this hodgepodged thing
class InductionHypothesis:
  """The implication "exists [induction_variable], forall [other variables], hypotheses => conclusions"."""
  
  def __init__(self, hypotheses: Sequence[Equality], conclusion: Equality, induction_variable: Variable):
    self.hypotheses = hypotheses
    self.conclusion = conclusion
    self.induction_variable = induction_variable
  
  @staticmethod
  def _try_union_assignments(assignment, source) -> bool:
    """Attempt to merge source to assignment, and return True if successful or False if there is a conflict."""
    
    for var, val in source.items():
      if var in assignment:
        if assignment[var] != val:
          # two different values for a variable => no valid assignment
          # example where this could happen: hyp_expr (a+b)+(b+a), eq_expr (0+0)+(0+S(0))
          return False
      else:
        assignment[var] = val
    
    return True
  
  def _find_assignment_in_expr(self, hyp_expr: Natural, eq_expr: Natural) -> Dict[Variable, Natural]:
    """Attempt to assign free variables in hyp_expr to expressions in eq_expr, or return None if this can't be done."""
    
    if isinstance(hyp_expr, Variable):
      # we can replace anything with a single variable (not the induction variable though)
      return None if hyp_expr == self.induction_variable else {hyp_expr: eq_expr}
    
    if type(hyp_expr) is not type(eq_expr):
      # mismatched expression types can't work
      return None
    
    # union all the child assignments together and check for consistency
    assignment = {}
    
    for i, hyp_child in enumerate(hyp_expr.children()):
      child_assignment = self._find_assignment_in_expr(hyp_child, eq_expr.children()[i])
      
      if child_assignment is None:
        # can't be done in the child => can't be done in the parent
        return None
      
      # union with the ongoing one
      if not InductionHypothesis._try_union_assignments(assignment, child_assignment):
        return None # conflict
    
    return assignment
  
  def _find_assignment_for_permutation(self, hyp_permutation, eq_permutation) -> Dict[Variable, Natural]:
    """Find an assignment of free variables in this permutation, or return None if not possible."""
    
    # TODO do something like substituting the assignments we've already found instead of just checking that we
    # get the same assignment? like we did in get_consequences?
    
    assignment = {}
    
    for hyp in hyp_permutation:
      for eq in eq_permutation:
        expr_assignment = self._find_assignment_in_expr(hyp, eq)
        
        if expr_assignment is None or not InductionHypothesis._try_union_assignments(assignment, expr_assignment):
          return None # conflict
    
    return assignment
  
  def _find_assignments(self, hypothesis: Equality, equality: Equality) -> List[Dict[Variable, Natural]]:
    """
    Find all possible assignments of free variables in the equality that satisfy the hypothesis, ignoring those not present.
    Return None if this is not possible.
    """
    
    # this is O(factorial(len(hypothesis.items)) * factorial(len(equality.items))) = O(scary)
    # each permutation of hypothesis.items and equality.items could generate another assignment, so we should check them all
    # TODO can we avoid ultra-factorial time here? substituting?
    
    assignments = []
    
    for hyp_permutation in itertools.permutations(hypothesis.items):
      for eq_permutation in itertools.permutations(equality.items):
        assignment = self._find_assignment_for_permutation(hyp_permutation, eq_permutation)
        
        if assignment is not None and assignment not in assignments:
          assignments.append(assignment)
    
    return assignments
  
  def _get_consequences_for_hypotheses(self, hypotheses, equality, assignment) -> Set[Equality]:
    """Recursive helper for get_consequences. Get all consequences, or the empty set if not satisfied."""
    
    # we find assignments in the first, sub in the rest, repeat until all satisfied (or one isn't)
    # this assumes the conclusions generated aren't affected by the order of the hypotheses
    # this could very possibly be invalid, in which case we'd have like O(n!m!k!) complexity (instead of O(n!m!), so much better)
    
    if not hypotheses:
      # none left: sub in the conclusion
      concl_vars = find_variables(self.conclusion)
      if any(var != self.induction_variable and var not in assignment for var in concl_vars):
        # unsubbed variables - FIXME could be a bug here if we don't want to sub all the variables?
        return None
      
      conclusion = self.conclusion
      for var, val in assignment.items():
        conclusion = substitute_variable(var, val, conclusion)
      
      return {conclusion}
    
    # get assignments from the first
    hyp_assignments = self._find_assignments(hypotheses[0], equality)
    
    if hyp_assignments is None:
      # no possible assignments
      return set()
    
    conclusions = set()
    
    for hyp_assignment in hyp_assignments:
      # try to merge it
      next_assignment = assignment[:]
      
      if not InductionHypothesis._try_union_assignments(next_assignment, hyp_assignment):
        continue # conflict
      
      # sub in all the rest
      next_hypotheses = copy.deepcopy(hypotheses[1:])
      next_hypotheses = substitute_variable(var, val, next_hypotheses)
      
      # sub in the next conclusion
      next_conclusions = self._get_consequences_for_hypotheses(next_hypotheses, equality, next_assignment)
      conclusions.update(next_conclusions)
    
    return conclusions
  
  def get_consequences(self, equality) -> Set[Equality]:
    """Find all possible assignments of free variables in equality that satisfy hypotheses and return conclusions entailed."""
    
    return self._get_consequences_for_hypotheses(self.hypotheses, equality, {})
  
  def __str__(self):
    return 'there exists a {} such that ({}) => ({})'.format(
      self.induction_variable, ' and '.join(map(str, self.hypotheses)), self.conclusion)


class Proof: # common proof superclass
  
  @staticmethod
  def _hypotheses_to_str(hypotheses):
    return ' and '.join(map(str, hypotheses))


class ImplicationProof(Proof):
  """A series of steps proving an implication of the form A & B & ... => C."""
  
  def __init__(self, hypotheses, conclusion, induction_hypotheses=[]):
    self.hypotheses = hypotheses
    self.conclusion = conclusion
    self.induction_hypotheses = induction_hypotheses
    self.steps = [] # Each step is (Equality, str justification)
  
  def add_step(self, equality, justification):
    self.steps.append((equality, justification))
  
  def text(self):
    text = f'Suppose {Proof._hypotheses_to_str(self.induction_hypotheses + self.hypotheses)}.\n'
    for i, step in enumerate(self.steps):
      text += f'{i+1}. {step[0]} (by {step[1]})\n'
    text += f'Therefore {self.conclusion}.'
    return text
  
  def __str__(self):
    return f'Proposition. ({Proof._hypotheses_to_str(self.hypotheses)}) => ({self.conclusion}).\nProof. {self.text()} QED.'


class InductionProof(Proof):
  """A proof using P5: P(x) is proven by proving P(0) and P(n) => P(S(n))."""
  
  def __init__(self, hypotheses, conclusion, base_case: Proof, inductive_step: Proof, variable: Variable):
    self.hypotheses = hypotheses
    self.conclusion = conclusion
    self.base_case = base_case
    self.inductive_step = inductive_step
    self.variable = variable
  
  def text(self):
    return f"""Proof by induction on {self.variable}.
Base case: {self.base_case.text()}
Inductive step: {self.inductive_step.text()}"""
  
  def __str__(self):
    return f"""Proposition. ({Proof._hypotheses_to_str(self.hypotheses)}) => ({self.conclusion}).
{self.text()}
Therefore {self.conclusion} by P5. QED."""


def prove_implication_directly(hypotheses: Sequence[Equality], conclusion: Equality, induction_hypotheses=[]) -> ImplicationProof:
  """Perform an exaustive search for a direct proof of hypotheses => conclusion, or return None if no proof can be found."""
  
  # the world's least efficient symbol manipulation routine
  # we're just going to keep stock of all the equalities and give up when the size no longer changes
  # this will run forever on any more complicated axiomatic system, probably
  # this is a breadth-first search, essentially
  
  proof = ImplicationProof(copy.deepcopy(hypotheses), copy.deepcopy(conclusion))
  
  if conclusion in hypotheses:
    return proof # well that was easy
  
  equalities = list(hypotheses)
  explore_queue = [(expr, hypot) for hypot in hypotheses for expr in hypot.items] # list of (expr, equality)
  
  # just fill in all the equalities we can, what could go wrong
  while explore_queue:
    member, eq = explore_queue.pop(0) # inefficient but whatever
    
    exprs = member.equal_exprs()
    
    for expr, steps in exprs:
      if expr not in eq.item_set and (expr, eq) not in explore_queue:
        eq.add_item(expr)
        explore_queue.append((expr, eq))
        
        for equality, justification in steps:
          proof.add_step(equality, justification) # BAD BAD BAD
        
        # transitivity
        if member != eq.representative:
          proof.add_step(Equality(eq.representative, expr), T) # proactive transitivity is probably bad
        
        if conclusion.item_set.issubset(eq.item_set):
          # just to make it look nicer, add another transitivity step
          if conclusion.items != [eq.representative, expr] and conclusion.items != [expr, eq.representative]:
            proof.add_step(conclusion, T)
          return proof
    
    # try the induction hypotheses on the equality
    for induction_hypothesis in induction_hypotheses:
      for entailed_equality in induction_hypothesis.get_consequences(eq):
        new_equality = True
        
        # try to associate it with an equality
        for equality in equalities:
          if not equality.item_set.isdisjoint(entailed_equality.item_set):
            # it's part of this equality
            
            if entailed_equality.item_set.issubset(equality.item_set):
              # nothing new is added, abort mission
              new_equality = False
              break
            
            # add all the new items to it
            for item in entailed_equality.items:
              if item not in equality.item_set:
                equality.add_item(item)
                explore_queue.append(item)
            
            break # we've found the equality, no need to keep going
        else:
          # we didn't break: no equality found, add a new one
          equalities.append(entailed_equality)
          explore_queue += entailed_equality.items
        
        if new_equality:
          proof.add_step(entailed_equality, ASSUMPTION)
  
  return None # we've looked everywhere and found nothing


def prove_implication_by_induction(
    hypotheses: Sequence[Equality], conclusion: Equality, induction_variable: Variable, induction_hypotheses=[]) -> InductionProof:
  """Prove hypotheses => conclusion by induction on induction_variable."""
  print('Proving induction on', induction_variable)
  print('substituted:', list(map(str, substitute_variable(induction_variable, ZERO, *hypotheses))))
  
  # first the base case: sub in 0 and prove
  base_case = prove_implication(
    substitute_variable(induction_variable, ZERO, *hypotheses),
    substitute_variable(induction_variable, ZERO, conclusion)[0])
  
  if not base_case:
    # not true for base case => can't prove it
    return None
  
  print('Base case:', base_case)
  
  # then the inductive step: P(k) => P(S(k))
  successor = Successor(induction_variable)
  inductive_step = prove_implication(
    substitute_variable(induction_variable, successor, *hypotheses),
    substitute_variable(induction_variable, successor, conclusion)[0],
    induction_hypotheses=[*induction_hypotheses, InductionHypothesis(hypotheses, conclusion, induction_variable)])
  
  if not inductive_step:
    return None
  
  return InductionProof(hypotheses, conclusion, base_case, inductive_step, induction_variable)


def prove_implication(hypotheses: Sequence[Equality], conclusion: Equality, induction_hypotheses=[]) -> Proof:
  """
  Prove hypotheses => conclusion with multiple methods until one works, or return None.
  All variables are assumed universally quantified ("for all").
  """
  # TODO don't assume all variables to be universally quantified
  
  print('hypotheses:', list(map(str, hypotheses)))
  print('induction hypotheses:', list(map(str, induction_hypotheses)))
  print('conclusion:', conclusion)
  
  # first try a direct proof
  proof = prove_implication_directly(copy.deepcopy(hypotheses), conclusion, induction_hypotheses)
  if proof:
    return proof
  
  # then try induction on each of the variables in the hypothesis
  print(list(map(str, hypotheses)))
  for variable in find_variables(*hypotheses):
    print('Trying induction on', variable)
    proof = prove_implication_by_induction(copy.deepcopy(hypotheses), conclusion, variable, induction_hypotheses)
    if proof:
      return proof
    print('Gave up induction on', variable)
  
  # give up
  return None
