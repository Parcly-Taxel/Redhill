module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Redhill.Odd.Defs
public import Redhill.Common.Conjectures

@[expose] public section

namespace OddCase

variable {n : ℕ} {F : Finset ℕ} {x : ℤ}

lemma tup_mem_factorFreeTuples
    (hn : Even n) (dx : ↑(Y n F) ∣ x) (dF : Disjoint {0, 1, 2, 5, 10} F) :
    tup n F x ∈ factorFreeTuples F (n + 5) := by
  simp only [factorFreeTuples, Set.mem_setOf_eq, sum_tup, pairwiseCoprime_tup hn dx, true_and]
  refine ⟨?_, not_dvd_tup dx dF⟩
  sorry

end OddCase

/-- Theorem 1.13. -/
theorem quality_factorFreeTuples_ge_of_odd_of_disjoint
    {n : ℕ} {F : Finset ℕ} (hn : 5 ≤ n ∧ Odd n) (dF : Disjoint {0, 1, 2, 5, 10} F) :
    5 / 3 ≤ quality (factorFreeTuples F n) := by
  sorry
