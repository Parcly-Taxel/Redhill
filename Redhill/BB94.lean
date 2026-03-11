module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Redhill.Defs
public import Redhill.ToMathlib.Coprime

@[expose] public section

namespace BB94

/-- The coefficient of `x^j` in the paper's `f_k(x)`. This is [OEIS A111125](https://oeis.org/A111125). -/
def fCoeff (k j : ℕ) : ℕ :=
  (k + j + 1).choose (2 * j + 1) * (2 * k + 1) / (k + j + 1)

end BB94

/-- Theorem 1.3 in the paper, Browkin and Brzeziński (1994). -/
lemma le_quality_nConjectureTuples {n : ℕ} (hn : 3 ≤ n) :
    (2 * n - 5 : ℕ) ≤ quality (nConjectureTuples n) := by
  sorry
