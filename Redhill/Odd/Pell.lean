module

public import Mathlib.Algebra.Ring.Int.Defs

@[expose] public section

namespace OddCase

/-- An infinite sequence of pairs of integers `(s, t)` satisfying
`y * s ^ 2 + 1 = (y + 1) * t ^ 2`. This will be applied with `y = Y n F ^ 2`,
hence the R for root. -/
def pellR (y : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 =>
    let (s, t) := pellR y n
    ((2 * y + 1) * s + (2 * y + 2) * t, 2 * y * s + (2 * y + 1) * t)

lemma pellR_spec {n y : ℕ} : y * (pellR y n).1 ^ 2 + 1 = (y + 1) * (pellR y n).2 ^ 2 := by
  induction n <;> grind [pellR]

end OddCase
