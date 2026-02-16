import Redhill.Defs

variable {n : ℕ} (hn : 3 ≤ n)

theorem strongNConjecture_three : StrongNConjecture 3 ↔ ABCConjecture := by
  sorry

include hn in
/- Theorem 1.3 in the paper, Browkin and Brzeziński (1994). -/
lemma le_quality_nConjectureMultisets : (2 * n - 5 : ℕ) ≤ quality (nConjectureMultisets n) := by
  sorry
