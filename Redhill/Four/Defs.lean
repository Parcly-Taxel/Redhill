/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Redhill.Common.Conjectures
public import Redhill.ToMathlib.Bezout

/-!
# Ramaekers's conjecture is false for `n = 4`

This construction was originally found by Tom Adamczewski using GPT-6
and posted at https://github.com/tadamcz/n-conjecture-strong.
The port to Redhill was done by me without any (further) LLM usage whatsoever.
-/

@[expose] public section

namespace FourCase

open Int Fin

/-- The sequence of 4-tuples containing an infinite subsequence in `ramaekersTuples`
whose qualities tend to `9 / 8`. -/
def tup (u : ℤ) : Fin 4 → ℤ
  | 0 => u ^ 9
  | 1 => (8 - u) ^ 5 * (u ^ 2 + 20 * u + 280) ^ 2
  | 2 => -105 * (2 * u - 3) ^ 6
  | 3 => 130032 * u ^ 4 + 10728480 * u ^ 3 - 202978980 * u ^ 2 + 1238324220 * u - 2568934655

/-- The LCM of all moduli needed to prove pairwise coprimality.
The original repository's `M` is four times this. -/
abbrev M : ℤ := 2 * 3 * 5 * 7 * 13 * 23 * 41 * 103 * 113 * 127 * 149 * 197 * 439 * 1249 *
  395119 * 649541 * 399635598557777987

variable {u : ℤ}

lemma sum_tup : ∑ i, tup u i = 0 := by
  simp only [tup, sum_univ_four]
  ring

section Coprime

open IsCoprime

lemma quartic_modEq {n : ℤ} (mu : u ≡ 19 [ZMOD n]) :
    130032 * u ^ 4 + 10728480 * u ^ 3 - 202978980 * u ^ 2 + 1238324220 * u - 2568934655 ≡
    130032 * 19 ^ 4 + 10728480 * 19 ^ 3 - 202978980 * 19 ^ 2 + 1238324220 * 19 - 2568934655
    [ZMOD n] :=
  (mu.pow 4).mul_left 130032 |>.add ((mu.pow 3).mul_left 10728480) |>.sub
  ((mu.pow 2).mul_left 202978980) |>.add (mu.mul_left 1238324220) |>.sub_right 2568934655

lemma isCoprime_zero_one (mu : u ≡ 19 [ZMOD 70]) : IsCoprime (tup u 0) (tup u 1) := by
  have cu : IsCoprime u 70 := by
    obtain ⟨t, e⟩ := modEq_iff_add_fac.mp (mu.mul_left (-11))
    exact ⟨-11, t + 3, by lia⟩
  rw [show (70 : ℤ) = 2 * 35 by lia, mul_right_iff] at cu
  refine ((pow_right ?_).mul_right (pow_right ?_)).pow_left
  · rw [show 8 - u = 2 ^ 3 - 1 * u by lia, sub_mul_right_right_iff]
    exact cu.1.pow_right
  · rw [show u ^ 2 + 20 * u + 280 = u * (u + 20) + 2 ^ 3 * 35 by lia, mul_add_left_right_iff]
    exact cu.1.pow_right.mul_right cu.2

lemma isCoprime_zero_two (mu : u ≡ 19 [ZMOD 105]) : IsCoprime (tup u 0) (tup u 2) := by
  refine ((neg_right ?_).mul_right (pow_right ?_)).pow_left
  · exact isCoprime_bezout_left mu (by decide)
  · have m₁ : u ≡ 19 [ZMOD 3] := mu.of_dvd (by decide)
    exact isCoprime_bezout ⟨2, -1, by lia⟩ m₁ ((m₁.mul_left 2).sub_right 3) (by decide)

lemma isCoprime_zero_three (mu : u ≡ 19 [ZMOD 2568934655]) : IsCoprime (tup u 0) (tup u 3) :=
  pow_left <| isCoprime_bezout
    ⟨130032 * u ^ 3 + 10728480 * u ^ 2 - 202978980 * u + 1238324220, -1, by grind [tup]⟩
    mu (quartic_modEq mu) (by decide)

lemma isCoprime_one_two (mu : u ≡ 19 [ZMOD M]) : IsCoprime (tup u 1) (tup u 2) := by
  have m₁ : u ≡ 19 [ZMOD 105] := mu.of_dvd (by decide)
  have m₂ : u ≡ 19 [ZMOD 13] := mu.of_dvd (by decide)
  have m₃ : u ≡ 19 [ZMOD 1249] := mu.of_dvd (by decide)
  refine (neg_right ?_).mul_right (pow_right ?_) <;> refine (pow_left ?_).mul_left (pow_left ?_)
  · exact isCoprime_bezout_left (m₁.sub_left 8) (by decide)
  · exact isCoprime_bezout_left (((m₁.pow 2).add (m₁.mul_left 20)).add_right 280) (by decide)
  · exact isCoprime_bezout ⟨2, 1, by lia⟩ (m₂.sub_left 8) ((m₂.mul_left 2).sub_right 3) (by decide)
  · exact isCoprime_bezout ⟨4, -2 * u - 43, by lia⟩
      (((m₃.pow 2).add (m₃.mul_left 20)).add_right 280) ((m₃.mul_left 2).sub_right 3) (by decide)

lemma isCoprime_one_three (mu : u ≡ 19 [ZMOD M]) : IsCoprime (tup u 1) (tup u 3) := by
  have m₁ : u ≡ 19 [ZMOD 372597217] := mu.of_dvd (by decide)
  have m₂ : u ≡ 19 [ZMOD 2084099646478812202205] := mu.of_dvd (by decide)
  refine (pow_left ?_).mul_left (pow_left ?_)
  · exact isCoprime_bezout
      ⟨130032 * u ^ 3 + 11768736 * u ^ 2 - 108829092 * u + 367691484, 1, by grind [tup]⟩
      (m₁.sub_left 8) (quartic_modEq m₁) (by decide)
  · exact isCoprime_bezout ⟨182081828432448 * u ^ 3 + 12162857834916432 * u ^ 2 -
      513984089089536720 * u + 7388067383983043940, -1400284764 * u - 6010576771, by grind [tup]⟩
      (((m₂.pow 2).add (m₂.mul_left 20)).add_right 280) (quartic_modEq m₂) (by decide)

lemma isCoprime_two_three (mu : u ≡ 19 [ZMOD M]) : IsCoprime (tup u 2) (tup u 3) := by
  have m₁ : u ≡ 19 [ZMOD 105] := mu.of_dvd (by decide)
  have m₂ : u ≡ 19 [ZMOD 1131284123] := mu.of_dvd (by decide)
  refine (neg_left ?_).mul_left (pow_left ?_)
  · exact isCoprime_bezout_right (quartic_modEq m₁) (by decide)
  · exact isCoprime_bezout
      ⟨65016 * u ^ 3 + 5461764 * u ^ 2 - 93296844 * u + 479216844, -1, by grind [tup]⟩
      ((m₂.mul_left 2).sub_right 3) (quartic_modEq m₂) (by decide)

lemma pairwiseCoprime_tup (mu : u ≡ 19 [ZMOD M]) : PairwiseCoprime (tup u) := by
  refine Pairwise.of_lt fun i j hij ↦ ?_
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
    i = 0 ∧ j = 1 ∨ i = 0 ∧ j = 2 ∨ i = 0 ∧ j = 3 ∨
    i = 1 ∧ j = 2 ∨ i = 1 ∧ j = 3 ∨ i = 2 ∧ j = 3 := by lia
  · exact isCoprime_zero_one (mu.of_dvd (by decide))
  · exact isCoprime_zero_two (mu.of_dvd (by decide))
  · exact isCoprime_zero_three (mu.of_dvd (by decide))
  · exact isCoprime_one_two mu
  · exact isCoprime_one_three mu
  · exact isCoprime_two_three mu

end Coprime

end FourCase

--theorem not_ramaekersConjecture_four : ¬RamaekersConjecture 4 := by
--  sorry
