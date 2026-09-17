/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Redhill.Common.Conjectures
public import Redhill.ToMathlib.Bezout
public import Redhill.ToMathlib.NatAbs

/-!
# Ramaekers's conjecture is false for `n = 4`

This construction was originally found by Tom Adamczewski using GPT-6
and posted at https://github.com/tadamcz/n-conjecture-strong.
The port to Redhill was done by me without any (further) LLM usage whatsoever.
-/

@[expose] public section

namespace FourCase

open Int Fin

/-- An abbreviation for the irreducible quartic polynomial that is the tuple's last term. -/
abbrev Q (u : ℤ) : ℤ :=
  130032 * u ^ 4 + 10728480 * u ^ 3 - 202978980 * u ^ 2 + 1238324220 * u - 2568934655

/-- The sequence of 4-tuples containing an infinite subsequence in `ramaekersTuples`
whose qualities tend to `9 / 8`. -/
def tup (u : ℤ) : Fin 4 → ℤ
  | 0 => u ^ 9
  | 1 => (8 - u) ^ 5 * (u ^ 2 + 20 * u + 280) ^ 2
  | 2 => -105 * (2 * u - 3) ^ 6
  | 3 => Q u

/-- The LCM of all moduli needed to prove pairwise coprimality.
The original repository's `M` is four times this. -/
abbrev M : ℤ :=
  2 * 3 * 5 * 7 * 13 * 23 * 41 * 103 * 113 * 127 * 149 * 197 * 439 * 1249 * 395119 * 649541 *
  399635598557777987

variable {u : ℤ}

lemma sum_tup : ∑ i, tup u i = 0 := by
  simp only [tup, sum_univ_four]
  ring

section Coprime

open IsCoprime

lemma Q_modEq {n : ℤ} (mu : u ≡ 19 [ZMOD n]) : Q u ≡ Q 19 [ZMOD n] :=
  (mu.pow 4).mul_left _ |>.add ((mu.pow 3).mul_left _) |>.sub ((mu.pow 2).mul_left _) |>.add
    (mu.mul_left _) |>.sub_right _

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
    mu (Q_modEq mu) (by decide)

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
      (m₁.sub_left 8) (Q_modEq m₁) (by decide)
  · exact isCoprime_bezout ⟨182081828432448 * u ^ 3 + 12162857834916432 * u ^ 2 -
      513984089089536720 * u + 7388067383983043940, -1400284764 * u - 6010576771, by grind [tup]⟩
      (((m₂.pow 2).add (m₂.mul_left 20)).add_right 280) (Q_modEq m₂) (by decide)

lemma isCoprime_two_three (mu : u ≡ 19 [ZMOD M]) : IsCoprime (tup u 2) (tup u 3) := by
  have m₁ : u ≡ 19 [ZMOD 105] := mu.of_dvd (by decide)
  have m₂ : u ≡ 19 [ZMOD 1131284123] := mu.of_dvd (by decide)
  refine (neg_left ?_).mul_left (pow_left ?_)
  · exact isCoprime_bezout_right (Q_modEq m₁) (by decide)
  · exact isCoprime_bezout
      ⟨65016 * u ^ 3 + 5461764 * u ^ 2 - 93296844 * u + 479216844, -1, by grind [tup]⟩
      ((m₂.mul_left 2).sub_right 3) (Q_modEq m₂) (by decide)

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

section Subsum

lemma tup_two_upper_bound (hu : 3 ≤ u.natAbs) :
    (-105 * (2 * u - 3) ^ 6).natAbs ≤ 76545 * u.natAbs ^ 6 := by
  simp_rw [natAbs_mul, natAbs_pow, reduceAbs, show 76545 = 105 * 3 ^ 6 by decide, mul_assoc,
    ← mul_pow]
  gcongr; lia

lemma Q_upper_bound (hu : 10728480 ≤ u.natAbs) : (Q u).natAbs ≤ 130036 * u.natAbs ^ 4 := by
  simp_rw [show 130036 = 130032 + 1 + 1 + 1 + 1 by rfl, add_one_mul]
  grw [natAbs_sub_le, natAbs_add_le, natAbs_sub_le, natAbs_add_le]
  simp_rw [natAbs_mul, natAbs_pow, reduceAbs]
  gcongr
  · rw [pow_succ' _ 3]; gcongr
  · rw [← two_add_two_eq_four, pow_add]
    rw [← Nat.pow_le_pow_iff_left two_ne_zero] at hu; gcongr; lia
  · rw [pow_succ _ 3]
    rw [← Nat.pow_le_pow_iff_left three_ne_zero] at hu; gcongr; lia
  · rw [← Nat.pow_le_pow_iff_left four_ne_zero] at hu; lia

lemma sum_tup_lt_tup_zero (hu : 10728480 ≤ u.natAbs) :
    ∑ i ∈ {0, 1}ᶜ, (tup u i).natAbs < (tup u 0).natAbs := by
  rw [show ({0, 1}ᶜ : Finset (Fin 4)) = {2, 3} by decide, Finset.sum_pair (by decide)]
  simp only [tup]
  calc
    _ ≤ 76545 * u.natAbs ^ 6 + 130036 * u.natAbs ^ 4 :=
      add_le_add (tup_two_upper_bound (by lia)) (Q_upper_bound hu)
    _ ≤ 76545 * u.natAbs ^ 6 + u.natAbs ^ 6 := by
      rw [add_le_add_iff_left, show 6 = 2 + 4 by rfl, pow_add]
      rw [← Nat.pow_le_pow_iff_left two_ne_zero] at hu
      gcongr; lia
    _ < _ := by
      rw [← add_one_mul, natAbs_pow, show 9 = 3 + 6 by rfl, pow_add]
      refine Nat.mul_lt_mul_of_pos_right ?_ (by positivity)
      rw [← Nat.pow_le_pow_iff_left three_ne_zero] at hu
      lia

lemma sum_tup_lt_tup_one (hu : 10728480 ≤ u.natAbs) :
    ∑ i ∈ {0, 1}ᶜ, (tup u i).natAbs < (tup u 1).natAbs := by
  rw [show ({0, 1}ᶜ : Finset (Fin 4)) = {2, 3} by decide, Finset.sum_pair (by decide)]
  simp only [tup]
  calc
    _ ≤ 76545 * u.natAbs ^ 6 + 130036 * u.natAbs ^ 4 :=
      add_le_add (tup_two_upper_bound (by lia)) (Q_upper_bound hu)
    _ ≤ 76545 * u.natAbs ^ 6 + u.natAbs ^ 6 := by
      rw [add_le_add_iff_left, show 6 = 2 + 4 by rfl, pow_add]
      rw [← Nat.pow_le_pow_iff_left two_ne_zero] at hu
      gcongr; lia
    _ ≤ 2449472 * (u.natAbs - 8) ^ 5 * u.natAbs := by
      rw [← add_one_mul, pow_succ, ← mul_assoc, show 2449472 = (76545 + 1) * 2 ^ 5 by decide,
        mul_assoc _ (2 ^ 5), ← mul_pow]
      gcongr; lia
    _ ≤ (8 - u).natAbs ^ 5 * u.natAbs ^ 2 := by
      rw [mul_rotate, sq, mul_assoc]
      gcongr <;> lia
    _ < _ := by
      simp only [natAbs_mul, natAbs_pow]
      refine mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left ?_ two_ne_zero) (Nat.pow_pos (by lia))
      rw [add_right_comm]
      refine (Nat.lt_sub_of_add_lt ?_).trans_le sub_le_add_natAbs
      rw [natAbs_mul, ← one_add_mul, natAbs_add_of_nonneg u.sq_nonneg (by decide)]
      calc
        _ < (u ^ 2).natAbs := by rw [sq, natAbs_mul]; gcongr; lia
        _ < _ := by lia

/-- `tup` with the first two terms added together. -/
def tupReduced (u : ℤ) : Fin 3 → ℤ
  | 0 => -105 * (2 * u - 3) ^ 6
  | 1 => Q u
  | 2 => 105 * (2 * u - 3) ^ 6 - Q u

lemma tupReduce_tup : tupReduce (tup u) {0, 1} (by simp) = tupReduced u := by
  ext i
  unfold tupReduce
  cases i using lastCases with
  | last =>
    simp_rw [lastCases_last, Finset.sum_pair zero_ne_one, tup, tupReduced, reduceLast]
    ring
  | cast i =>
    have : @complRank 4 2 {0, 1} (by simp) = (·.natAdd 2) := by
      refine (Finset.orderEmbOfFin_unique _ (fun i ↦ ?_) ?_).symm
      · fin_cases i <;> simp
      · exact (natAddOrderEmb 2).strictMono
    simp_rw [lastCases_castSucc, this, tup, tupReduced]
    fin_cases i <;> rfl

lemma tup_two_lower_bound (hu : 3 ≤ u.natAbs) :
    105 * u.natAbs ^ 6 ≤ (-105 * (2 * u - 3) ^ 6).natAbs := by
  simp_rw [natAbs_mul, natAbs_pow, reduceAbs]
  gcongr; lia

lemma sum_tupReduced_lt_tupReduced_zero (hu : 10728480 ≤ u.natAbs) :
    ∑ i ∈ {0, 2}ᶜ, (tupReduced u i).natAbs < (tupReduced u 0).natAbs := by
  rw [show ({0, 2}ᶜ : Finset (Fin 3)) = {1} by decide, Finset.sum_singleton]
  simp only [tupReduced]
  calc
    _ ≤ _ := Q_upper_bound hu
    _ < _ := by rw [pow_succ' _ 5, ← mul_assoc]; gcongr <;> lia
    _ ≤ _ := tup_two_lower_bound (by lia)

lemma sum_tupReduced_lt_tupReduced_two (hu : 10728480 ≤ u.natAbs) :
    ∑ i ∈ {0, 2}ᶜ, (tupReduced u i).natAbs < (tupReduced u 2).natAbs := by
  rw [show ({0, 2}ᶜ : Finset (Fin 3)) = {1} by decide, Finset.sum_singleton, tupReduced, tupReduced,
    sub_eq_add_neg]
  refine (Nat.lt_sub_of_add_lt ?_).trans_le sub_le_add_natAbs
  rw [natAbs_neg, ← two_mul]
  calc
    _ ≤ _ := Nat.mul_le_mul_left _ (Q_upper_bound hu)
    _ < 105 * u.natAbs ^ 6 := by rw [pow_succ' _ 5, ← mul_assoc, ← mul_assoc]; gcongr <;> lia
    _ ≤ _ := by
      conv_rhs => rw [← natAbs_neg, ← neg_mul]
      exact tup_two_lower_bound (by lia)

lemma tupReduce_tupReduced : tupReduce (tupReduced u) {0, 2} (by simp) = ![Q u, -Q u] := by
  ext i
  unfold tupReduce
  cases i using lastCases with
  | last =>
    rw [lastCases_last, Finset.sum_pair (by decide), tupReduced, tupReduced]
    simp_rw [reduceLast, Matrix.cons_val]
    ring
  | cast i =>
    have : @complRank 3 1 {0, 2} (by simp) = ![1] :=
      (Finset.orderEmbOfFin_unique _ (by simp) (by decide)).symm
    simp_rw [lastCases_castSucc, this, tupReduced]
    fin_cases i; rfl

lemma Q_le_neg_tup_two (hu : 10728480 ≤ u.natAbs) : Q u ≤ 105 * (2 * u - 3) ^ 6 := calc
  _ ≤ _ := le_natAbs
  _ ≤ 130036 * u.natAbs ^ 4 := mod_cast Q_upper_bound hu
  _ ≤ 130036 * (2 * u - 3) ^ 4 := by
    refine mul_le_mul_of_nonneg_left ?_ (by decide)
    simp only [show 4 = 2 * 2 by rfl, pow_mul, sq_le_sq, abs_pow]
    grind
  _ ≤ _ := by
    rw [pow_add _ 2 4, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    suffices 40 ^ 2 ≤ (2 * u - 3) ^ 2 by lia
    rw [sq_le_sq]
    grind

lemma Q_pos (hu : 100 ≤ u.natAbs) : 0 < Q u := by
  obtain lu | gu : 0 ≤ u - 19 ∨ 100 ≤ -u := by lia
  · rw [show Q u = u ^ 2 * (130032 * u ^ 2 + 10728480 * (u - 19) + 862140) +
      (1238324220 * u - 2568934655) by ring]
    have : 0 < 1238324220 * u - 2568934655 := by lia
    positivity
  · rw [sub_pos, ← sub_lt_iff_lt_add, lt_sub_iff_add_lt, ← sub_lt_iff_lt_add]
    calc
      _ < 26 * (-u) ^ 4 + 1239 * (-u) ^ 4 + 20298 * (-u) ^ 4 + 107285 * (-u) ^ 4 := by
        iterate 2 rw [sub_eq_add_neg, ← mul_neg]
        gcongr ?_ + ?_ + ?_ + ?_
        · have := pow_le_pow_left₀ (by decide) hu 4; lia
        · have := pow_le_pow_left₀ (by decide) hu 3
          rw [pow_succ, ← mul_assoc]; gcongr; lia
        · have := pow_le_pow_left₀ (by decide) hu 2
          rw [← neg_sq, ← two_add_two_eq_four, pow_add, ← mul_assoc]; gcongr; lia
        · rw [← Odd.neg_pow (by decide), pow_succ' _ 3, ← mul_assoc]; gcongr; lia
      _ ≤ _ := by
        simp_rw [(show Even 4 by decide).neg_pow, ← add_mul]
        exact mul_le_mul_of_nonneg_right (by decide) (by positivity)

lemma strongSSC_tup (hu : 10728480 ≤ u.natAbs) : StrongSSC (tup u) := by
  have key : IsSubsumBlock (tup u) {0, 1} := by
    apply IsSubsumBlock.pair_of_sum_natAbs_lt (sum_tup_lt_tup_zero hu) (sum_tup_lt_tup_one hu)
    simp only [tup, ← mul_assoc]
    refine mul_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    obtain lu | gu := le_total 0 u
    · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (Odd.pow_nonpos (by decide) (by lia))
    · exact mul_nonpos_of_nonpos_of_nonneg (Odd.pow_nonpos (by decide) gu) (Int.pow_nonneg (by lia))
  apply key.strongSSC_tupReduce
  rw [tupReduce_tup]
  have key2 : IsSubsumBlock (tupReduced u) {0, 2} := by
    apply IsSubsumBlock.pair_of_sum_natAbs_lt (sum_tupReduced_lt_tupReduced_zero hu)
      (sum_tupReduced_lt_tupReduced_two hu)
    simp only [tupReduced, neg_mul, Int.neg_nonpos_iff]
    apply mul_nonneg (by positivity)
    rw [sub_nonneg]
    exact Q_le_neg_tup_two hu
  apply key2.strongSSC_tupReduce
  rw [tupReduce_tupReduced]
  apply strongSSC_pair
  simp_rw [zero_eta, Matrix.cons_val]
  exact (Q_pos (by lia)).ne'

end Subsum

end FourCase

--theorem not_ramaekersConjecture_four : ¬RamaekersConjecture 4 := by
--  sorry
