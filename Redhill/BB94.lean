import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Redhill.Defs
import Redhill.ToMathlib.Coprime

/-- Theorem 1.3 in the paper, Browkin and Brzeziński (1994). -/
lemma le_quality_nConjectureTuples {n : ℕ} (hn : 3 ≤ n) :
    (2 * n - 5 : ℕ) ≤ quality (nConjectureTuples n) := by
  sorry
