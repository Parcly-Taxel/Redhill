module

public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Redhill.Common.PairwiseCoprime
public import Redhill.Common.PrimeChain
public import Redhill.Common.VWPair
public import Redhill.ToMathlib.Coprime

/-!
In this section `l ≥ 11` is an upper bound on F, i.e. wlog `F = Icc 3 l`,
while `h` is the variable such that `tup n l h ∈ factorFreeTuples F (n + 6)`
for sufficiently large `h`.
-/

@[expose] public section

namespace GeneralCase

open Nat Fin Finset

variable (n l h : ℕ)

/-- `y` in the paper, fixing `t = 102`. -/
def Y : ℕ := 102 * l !

/-- `x` in the paper. -/
def X : ℕ := (Y l + 1) ^ h !

/-- Sufficient conditions for `tup n l h ∈ factorFreeTuples F (n + 6)`. -/
structure Conditions : Prop where
  /-- `l ≥ 11` -/
  l_ge : 11 ≤ l
  /-- `x ≡ 1` mod `10y+1` -/
  X_modEq_succ : X l h ≡ 1 [MOD (10 * Y l + 1)]
  /-- `x ≡ 1` mod `10y-1` -/
  X_modEq_pred : X l h ≡ 1 [MOD (10 * Y l - 1)]

variable {n l h}

end GeneralCase
