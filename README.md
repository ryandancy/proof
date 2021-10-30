An attempt at an automated theorem prover for Peano arithmetic.

Given a basic arithmetic fact, `prove_implication` will attempt to prove it, and will generate a human-readable proof if it finds one. For example, the following generates a proof that 1 + 1 = 2 (or using `S` as the successor function, `S(0) + S(0) = S(S(0))`).
```py
>>> from peano import Variable as Var, Equality as Eq, Addition as Add, Successor as S, prove_implication, ZERO
>>> x = Var('x')
>>> print(prove_implication([Eq(x, Add(S(ZERO), S(ZERO)))], Eq(x, S(S(ZERO)))))
Proposition. (x = (S(0) + S(0))) => (x = S(S(0))).
Proof. Suppose x = (S(0) + S(0)).
1. (S(0) + S(0)) = S((S(0) + 0)) (by A2)
2. x = S((S(0) + 0)) (by transitivity of equality)
3. (S(0) + 0) = S(0) (by A1)
4. S((S(0) + 0)) = S(S(0)) (by substitution)
5. x = S(S(0)) (by transitivity of equality)
Therefore x = S(S(0)). QED.
```

We essentially recursively enumerate all possible consequences of the premises until we find the conclusion, and as such the algorithm will run forever if the proposition is not true. (Returning if the proposition is not true is actually impossible, because such an algorithm would solve the [Entscheidungsproblem](https://en.wikipedia.org/wiki/Entscheidungsproblem), which is undecidable.) There are also many cases where the algorithm will run prohibitively long.
