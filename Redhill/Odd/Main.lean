module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Redhill.Odd.Defs
public import Redhill.Common.Defs

@[expose] public section

namespace OddCase

open Nat Finset

end OddCase

/-- Theorem 1.13. -/
theorem quality_factorFreeTuples_ge_of_odd_of_disjoint
    {n : ℕ} {F : Finset ℕ} (hn : 5 ≤ n ∧ Odd n) (dF : Disjoint {0, 1, 2, 5, 10} F) :
    5 / 3 ≤ quality (factorFreeTuples F n) := by
  sorry
