/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Data.Int.ModEq
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Proving coprimality of integers through Bézout reduction
-/

public section

namespace Int

variable {x x' y y' c : ℤ}

/-- Suppose `a * x + b * y = c`. Then coprimality of `x, y` modulo `c` can be transferred to
`x, y` themselves. This is useful when `x, y` are polynomials and `c` is their resultant. -/
lemma isCoprime_bezout (bz : ∃ a b, a * x + b * y = c)
    (zmx : x ≡ x' [ZMOD c]) (zmy : y ≡ y' [ZMOD c]) (cp : IsCoprime x' y') :
    IsCoprime x y := by
  obtain ⟨a, b, e⟩ := bz
  rw [isCoprime_iff_gcd_eq_one] at cp ⊢
  have gx := x.gcd_dvd_left y
  have gy := x.gcd_dvd_right y
  have gc := e ▸ dvd_add (gx.mul_left a) (gy.mul_left b)
  rw [(zmx.of_dvd gc).dvd_iff] at gx
  rw [(zmy.of_dvd gc).dvd_iff] at gy
  exact Nat.dvd_one.mp (cp ▸ dvd_gcd gx gy)

lemma isCoprime_bezout_left (zm : x ≡ x' [ZMOD c]) (cp : IsCoprime x' c) : IsCoprime x c :=
  isCoprime_bezout ⟨0, 1, by simp⟩ zm rfl cp

lemma isCoprime_bezout_right (zm : y ≡ y' [ZMOD c]) (cp : IsCoprime c y') : IsCoprime c y :=
  isCoprime_bezout ⟨1, 0, by simp⟩ rfl zm cp

end Int
