/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.RingTheory.Radical.NatInt
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
  exact strongSSC_pair (Q_pos (by lia)).ne'

end Subsum

/-- An infinite sequence of integers satisfying `2 * E n - 3 = 35 * (2 * M + 1) ^ n`. -/
def E : ℕ → ℤ
  | 0 => 19
  | k + 1 => (2 * M + 1) * E k - 3 * M

variable {k : ℕ}

lemma two_mul_E_sub_three : 2 * E k - 3 = 35 * (2 * M + 1) ^ k := by induction k <;> grind [E]

lemma E_modEq : E k ≡ 19 [ZMOD M] := by
  induction k with
  | zero => simp [E]
  | succ k ih =>
    rw [E, show (2 * M + 1) * E k - 3 * M = E k + M * (2 * E k - 3) by ring]
    exact modEq_add_fac_self.trans ih

lemma strictMono_E : StrictMono E := by
  refine strictMono_nat_of_lt_succ fun k ↦ ?_
  rw [← Int.mul_lt_mul_left zero_lt_two, ← sub_lt_sub_iff_right 3, two_mul_E_sub_three,
    two_mul_E_sub_three]
  gcongr <;> lia

lemma add_nineteen_le_E : k + 19 ≤ E k := by induction k <;> grind [E]

lemma injective_tup_E : (tup ∘ E).Injective := fun i j e ↦ by
  replace e := congr($e 0)
  simp_rw [Function.comp_apply, tup] at e
  rwa [Odd.pow_inj (by decide), strictMono_E.injective.eq_iff] at e

lemma strongSSC_tup_E : StrongSSC (tup (E k)) := by
  obtain rfl | hk : k = 0 ∨ 1 ≤ k := by lia
  · rw [StrongSSC, IsSubsumBlock]
    decide
  · apply strongSSC_tup
    have : 10728480 ≤ E k := (strictMono_E.monotone hk).trans' (by decide)
    lia

lemma tup_E_mem_factorFreeTuples : tup (E k) ∈ factorFreeTuples ∅ 4 :=
  ⟨sum_tup, strongSSC_tup_E, pairwiseCoprime_tup E_modEq, by simp⟩

lemma maxAbs_tup_E : maxAbs (tup (E k)) = (E k).natAbs ^ 9 := by
  simp_rw [maxAbs_eq_foldr, List.ofFn_succ, List.ofFn_zero, reduceSucc, List.foldr_cons,
    List.foldr_nil, tup, max_zero]
  obtain rfl | hk : k = 0 ∨ 1 ≤ k := by lia
  · decide
  have lE : 10728480 ≤ E k := (strictMono_E.monotone hk).trans' (by decide)
  have hu : 10728480 ≤ (E k).natAbs := by lia
  have e1 := sum_tupReduced_lt_tupReduced_zero hu
  simp_rw [show ({0, 2}ᶜ : Finset (Fin 3)) = {1} by decide, Finset.sum_singleton, tupReduced] at e1
  have e2 := sum_tup_lt_tup_one hu
  rw [show ({0, 1}ᶜ : Finset (Fin 4)) = {2, 3} by decide, Finset.sum_pair (by decide)] at e2
  replace e2 : (-105 * (2 * E k - 3) ^ 6).natAbs ≤
      ((8 - E k) ^ 5 * (E k ^ 2 + 20 * E k + 280) ^ 2).natAbs := by grind [tup]
  rw [max_eq_left e1.le, max_eq_left e2, ← natAbs_pow, max_eq_left_iff]
  have tnn : (8 - E k) ^ 5 * (E k ^ 2 + 20 * E k + 280) ^ 2 ≤ 0 := by
    rw [← neg_nonneg, ← neg_mul, ← Odd.neg_pow (by decide), neg_sub]
    have Epos : 0 < E k - 8 := by lia
    positivity
  suffices -((8 - E k) ^ 5 * (E k ^ 2 + 20 * E k + 280) ^ 2) ≤ E k ^ 9 by lia
  rw [neg_le_iff_add_nonneg, show E k ^ 9 + (8 - E k) ^ 5 * (E k ^ 2 + 20 * E k + 280) ^ 2 =
    105 * (2 * (E k) - 3) ^ 6 - Q (E k) by ring, sub_nonneg]
  exact Q_le_neg_tup_two hu

section Quality

open Real UniqueFactorizationMonoid

lemma radical_tup_E_dvd :
    ∃ C > 0, ∀ k,
    radical (∏ i, tup (E k) i) ∣ C * E k * (E k - 8) * (E k ^ 2 + 20 * E k + 280) * Q (E k) := by
  simp_rw [prod_univ_four, tup]
  refine ⟨105 * 35 * (2 * M + 1), by positivity, fun k ↦ ?_⟩
  grw [radical_mul_dvd, mul_dvd_mul ?_ radical_dvd_self]
  rw [← mul_rotate, ← mul_assoc]
  grw [radical_mul_dvd, radical_pow _ two_ne_zero, mul_dvd_mul ?_ radical_dvd_self]
  rw [show -105 * (2 * E k - 3) ^ 6 * E k ^ 9 * (8 - E k) ^ 5 =
    105 * (2 * E k - 3) ^ 6 * E k ^ 9 * (E k - 8) ^ 5 by ring]
  iterate 2 grw [radical_mul_dvd, radical_pow _ (by decide), mul_dvd_mul ?_ radical_dvd_self]
  rw [mul_assoc, two_mul_E_sub_three]
  grw [radical_mul_dvd, radical_pow _ (by decide), mul_dvd_mul radical_dvd_self]
  grw [radical_mul_dvd, mul_dvd_mul radical_dvd_self]
  grw [radical_pow_dvd]
  exact radical_dvd_self

lemma Q_E_pos : 0 < Q (E k) := by
  obtain rfl | hk : k = 0 ∨ 1 ≤ k := by lia
  · decide
  · have lE : 10728480 ≤ E k := (strictMono_E.monotone hk).trans' (by decide)
    have lQ := Q_pos (show 100 ≤ (E k).natAbs by lia)
    lia

lemma Q_E_upper_bound : Q (E k) ≤ 293248 * E k ^ 4 := by
  obtain rfl | hk : k = 0 ∨ 1 ≤ k := by lia
  · decide
  · have lE : 10728480 ≤ E k := (strictMono_E.monotone hk).trans' (by decide)
    have lQ := Q_upper_bound (show 10728480 ≤ (E k).natAbs by lia)
    lia

lemma radical_tup_E_le : ∃ C > 0, ∀ k, radical (∏ i, tup (E k) i) ≤ C * E k ^ 8 := by
  obtain ⟨C, Cpos, hC⟩ := radical_tup_E_dvd
  refine ⟨3 * 293248 * C, by positivity, fun k ↦ ?_⟩
  rw [show 3 * 293248 * C * E k ^ 8 = C * E k * E k * (3 * E k ^ 2) * (293248 * E k ^ 4) by ring]
  have lE : 19 ≤ E k := strictMono_E.monotone k.zero_le
  have Epos : 0 < E k - 8 := by lia
  have Qpos := @Q_E_pos k
  have Qub := @Q_E_upper_bound k
  refine (le_of_dvd (by positivity) (hC k)).trans ?_
  gcongr
  · lia
  · rw [show 3 * E k ^ 2 = E k ^ 2 + (E k ^ 2 + (E k * (E k - 1) + E k)) by ring, add_assoc,
      add_le_add_iff_left, show 20 * E k + 280 = 19 * E k + (280 + E k) by ring, sq]
    gcongr
    calc
      _ ≤ (19 * 18 : ℤ) := by lia
      _ ≤ _ := by gcongr; lia

lemma le_tupleQuality :
    ∃ C, ∀ k, .ofReal (9 * log (E k) / (C + 8 * log (E k))) ≤ tupleQuality (tup (E k)) := by
  obtain ⟨C, Cpos, hC⟩ := radical_tup_E_le
  refine ⟨log C, fun k ↦ ?_⟩
  apply ENNReal.ofReal_le_ofReal
  rw [maxAbs_tup_E, Nat.cast_pow, Nat.cast_natAbs, cast_abs, log_pow, Nat.cast_ofNat, log_abs]
  apply div_le_div_of_nonneg_left (by positivity)
  · apply log_pos
    rw [← cast_one, cast_lt, one_lt_radical_iff]
    exact strongSSC_tup_E.one_lt_natAbs_prod (by lia)
  · have p8 : (E k ^ 8 : ℝ) ≠ 0 := by
      apply pow_ne_zero
      have : 19 ≤ E k := strictMono_E.monotone k.zero_le
      positivity
    rw [show (8 : ℝ) = (8 : ℕ) by rfl, ← log_pow, ← log_mul (by rw [cast_ne_zero]; lia) p8]
    exact log_le_log (mod_cast radical_pos _) (mod_cast hC _)

open Filter in
lemma liminf_tupleQuality_tup_E : 9 / 8 ≤ liminf (tupleQuality ∘ tup ∘ E) atTop := by
  obtain ⟨C, hC⟩ := le_tupleQuality
  refine le_of_eq_of_le ?_ (liminf_le_liminf (.of_forall hC))
  have e₁ : (9 / 8 : ENNReal) = ENNReal.ofReal (9 / 8) := by
    simp [ENNReal.ofReal_div_of_pos (show 0 < 8 by simp)]
  rw [e₁]
  refine (ENNReal.tendsto_ofReal ?_).liminf_eq.symm
  let f (k : ℕ) := log (E k)
  change Tendsto ((fun x ↦ 9 * x / (C + 8 * x)) ∘ f) atTop (nhds (9 / 8))
  have ttf : Tendsto f atTop atTop := by
    refine tendsto_log_atTop.comp (tendsto_intCast_atTop_atTop.comp ?_)
    exact tendsto_atTop_atTop_of_monotone strictMono_E.monotone fun b ↦
      ⟨(b - 19).natAbs, by grind [@add_nineteen_le_E (b - 19).natAbs]⟩
  refine Tendsto.comp ?_ ttf
  apply Tendsto.congr' (f₁ := fun x ↦ 9 / (C * x⁻¹ + 8))
  · exact (eventually_ne_atTop 0).mp (.of_forall fun _ _ ↦ by field)
  · refine tendsto_const_nhds.div ?_ (by simp)
    nth_rw 2 [show 8 = C * 0 + 8 by simp]
    exact (tendsto_inv_atTop_zero.const_mul _).add_const _

end Quality

end FourCase

open FourCase

theorem quality_factorFreeTuples_four_ge : 9 / 8 ≤ quality (factorFreeTuples ∅ 4) := by
  refine quality_ge_of_liminf_univ ⟨_, injective_tup_E⟩ ?_ liminf_tupleQuality_tup_E
  simp [tup_E_mem_factorFreeTuples]

theorem not_ramaekersConjecture_four : ¬RamaekersConjecture 4 := by
  have := quality_factorFreeTuples_four_ge.trans quality_factorFreeTuples_le_ramaekersTuples
  refine (this.trans_lt' ?_).ne'
  rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp)]
  norm_num
