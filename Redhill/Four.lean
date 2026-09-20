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

This construction was originally found by Tom Adamczewski using GPT-6 Astra
and posted at https://github.com/tadamcz/n-conjecture-strong.
The port to Redhill was done by me without any (further) LLM usage whatsoever.
-/

public section

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
    ⟨130032 * u ^ 3 + 10728480 * u ^ 2 - 202978980 * u + 1238324220, -1, by lia [tup]⟩
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
      ⟨130032 * u ^ 3 + 11768736 * u ^ 2 - 108829092 * u + 367691484, 1, by lia [tup]⟩
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
      ⟨65016 * u ^ 3 + 5461764 * u ^ 2 - 93296844 * u + 479216844, -1, by lia [tup]⟩
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

section Bounds

lemma Q_lower_bound (hu : 19 ≤ u) : 38216358337 ≤ Q u := calc
  _ = 19 ^ 2 * (130032 * 19 ^ 2 + 10728480 * (19 - 19) + 862140) +
    1238324220 * 19 - 2568934655 := by decide
  _ ≤ u ^ 2 * (130032 * u ^ 2 + 10728480 * (u - 19) + 862140) + 1238324220 * u - 2568934655 := by
    gcongr
  _ = _ := by ring

lemma Q_upper_bound (hu : 19 ≤ u) : (Q u).natAbs < 875230 * u.natAbs ^ 4 := by
  have nn : 0 ≤ 10728480 * u ^ 3 - 202978980 * u ^ 2 := by
    rw [sub_nonneg, pow_succ' _ 2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by lia) (by positivity)
  rw [Q, add_sub_assoc, add_sub_assoc, natAbs_add_of_nonneg (by positivity) (by lia),
    natAbs_add_of_nonneg (by positivity) nn]
  calc
    _ < (130032 * u ^ 4).natAbs + (10728480 * u ^ 3).natAbs + (1238324220 * u).natAbs := by
      gcongr
      · suffices 0 < 202978980 * u ^ 2 by lia
        positivity
      · lia
    _ ≤ 130032 * u.natAbs ^ 4 + 564657 * u.natAbs ^ 4 + 180541 * u.natAbs ^ 4 := by
      simp_rw [natAbs_mul, natAbs_pow, reduceAbs]
      gcongr _ + ?_ + ?_
      · rw [pow_succ' _ 3, ← mul_assoc]; gcongr; lia
      · grw [show 1238324220 ≤ 180541 * 19 ^ 3 by decide, pow_succ _ 3, ← mul_assoc]; gcongr; lia
    _ = _ := by ring

lemma tup_three_lt_neg_tup_two (hu : 19 ≤ u) : tup u 3 < -tup u 2 := calc
  _ ≤ _ := le_natAbs
  _ < 875230 * u.natAbs ^ 4 := mod_cast Q_upper_bound hu
  _ ≤ 79567 * (2 * u - 3) ^ 4 := by
    grw [show (875230 : ℤ) ≤ 79567 * 11 by decide, mul_assoc, natAbs_of_nonneg (by lia)]
    refine mul_le_mul_of_nonneg_left ?_ (by decide)
    obtain rfl | ⟨_, _⟩ : u = 19 ∨ 0 ≤ 5 * u - 96 ∧ 0 ≤ u - 1 := by lia
    · decide
    · rw [show (2 * u - 3) ^ 4 = (5 * u - 96) * u ^ 3 + 216 * u * (u - 1) + 81 + 11 * u ^ 4 by ring,
        le_add_iff_nonneg_left]
      positivity
  _ ≤ _ := by
    rw [tup, pow_add _ 2 4, neg_mul, neg_neg, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    grw [show (79567 : ℤ) ≤ 105 * 35 ^ 2 by decide]; gcongr; lia

lemma neg_tup_two_lt_tup_zero (hu : 19 ≤ u) : -tup u 2 < tup u 0 := calc
  _ = _ := by rw [tup, neg_mul, neg_neg]
  _ < 105 * (2 * u) ^ 6 := by gcongr <;> lia
  _ ≤ _ := by
    grw [tup, mul_pow, ← mul_assoc, show (105 : ℤ) * 2 ^ 6 ≤ 19 ^ 3 by decide, hu, pow_add _ 3 6]

lemma tup_three_lt_neg_tup_one (hu : 19 ≤ u) : tup u 3 < -tup u 1 := by
  lia [neg_tup_two_lt_tup_zero hu, tup]

lemma neg_tup_one_lt_tup_zero (hu : 19 ≤ u) : -tup u 1 < tup u 0 := by
  lia [tup_three_lt_neg_tup_two hu, tup]

end Bounds

/-- An infinite sequence of integers satisfying `2 * E n - 3 = 35 * (2 * M + 1) ^ n`. -/
def E : ℕ → ℤ
  | 0 => 19
  | k + 1 => (2 * M + 1) * E k - 3 * M

variable {k : ℕ}

lemma two_mul_E_sub_three : 2 * E k - 3 = 35 * (2 * M + 1) ^ k := by induction k <;> lia [E]

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

lemma add_nineteen_le_E : k + 19 ≤ E k := by induction k <;> lia [E]

lemma injective_tup_E : (tup ∘ E).Injective := fun i j e ↦ by
  replace e := congr($e 0)
  simp_rw [Function.comp_apply, tup] at e
  rwa [Odd.pow_inj (by decide), strictMono_E.injective.eq_iff] at e

lemma tup_E_ineq_package (k : ℕ) :
    1 < tup (E k) 3 ∧ tup (E k) 3 < -tup (E k) 2 ∧ tup (E k) 3 < -tup (E k) 1 ∧
    -tup (E k) 2 < tup (E k) 0 ∧ -tup (E k) 1 < tup (E k) 0 := by
  have hu : 19 ≤ E k := by lia [@add_nineteen_le_E k]
  exact ⟨(Q_lower_bound hu).trans_lt' (by decide), tup_three_lt_neg_tup_two hu,
    tup_three_lt_neg_tup_one hu, neg_tup_two_lt_tup_zero hu, neg_tup_one_lt_tup_zero hu⟩

lemma tup_E_mem_ramaekersTuples : tup (E k) ∈ ramaekersTuples 4 := by
  refine ⟨sum_tup, fun b n₁ n₂ hs ↦ ?_, pairwiseCoprime_tup E_modEq⟩
  rw [← Finset.card_pos] at n₁
  rw [← Finset.card_compl_lt_iff_nonempty, Fintype.card_fin, compl_compl] at n₂
  have := tup_E_ineq_package k
  obtain cb | cb | cb : b.card = 1 ∨ b.card = 2 ∨ b.card = 3 := by lia
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp cb
    rw [Finset.sum_singleton] at hs
    fin_cases i <;> lia
  · obtain ⟨i, j, hn, rfl⟩ := Finset.card_eq_two.mp cb
    rw [Finset.sum_pair hn] at hs
    fin_cases i <;> fin_cases j <;> lia
  · replace cb : bᶜ.card = 1 := by rw [Finset.card_compl, Fintype.card_fin]; lia
    rw [← @sum_tup (E k), ← Finset.sum_add_sum_compl b, left_eq_add] at hs
    obtain ⟨i, e⟩ := Finset.card_eq_one.mp cb
    rw [e, Finset.sum_singleton] at hs
    fin_cases i <;> lia

lemma maxAbs_tup_E : maxAbs (tup (E k)) = (E k).natAbs ^ 9 := by
  rw [show (E k).natAbs ^ 9 = (tup (E k) 0).natAbs by simp [tup]]
  refine maxAbs_eq_of_forall_le fun i ↦ ?_
  have := tup_E_ineq_package k
  fin_cases i <;> lia

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

lemma radical_tup_E_le : ∃ C > 0, ∀ k, radical (∏ i, tup (E k) i) ≤ C * E k ^ 8 := by
  obtain ⟨C, Cpos, hC⟩ := radical_tup_E_dvd
  refine ⟨2625690 * C, by positivity, fun k ↦ ?_⟩
  rw [show 2625690 * C * E k ^ 8 = C * E k * E k * (3 * E k ^ 2) * (875230 * E k ^ 4) by ring]
  have hu : 19 ≤ E k := by lia [@add_nineteen_le_E k]
  have hu' : 0 < E k - 8 := by lia
  have Qpos : 0 < Q (E k) := (Q_lower_bound hu).trans_lt' (by decide)
  refine (le_of_dvd (by positivity) (hC k)).trans ?_
  gcongr
  · lia
  · rw [show 3 * E k ^ 2 = E k ^ 2 + (E k ^ 2 + (E k * (E k - 1) + E k)) by ring, add_assoc,
      add_le_add_iff_left, show 20 * E k + 280 = 19 * E k + (280 + E k) by ring, sq]
    gcongr
    calc
      _ ≤ (19 * 18 : ℤ) := by lia
      _ ≤ _ := by gcongr; lia
  · have Qub := (Q_upper_bound hu).le
    rwa [← Nat.cast_le (α := ℤ), Nat.cast_mul, Nat.cast_pow, natAbs_of_nonneg (by lia),
      natAbs_of_nonneg (by lia)] at Qub

lemma le_tupleQuality :
    ∃ C, ∀ k, .ofReal (9 * log (E k) / (C + 8 * log (E k))) ≤ tupleQuality (tup (E k)) := by
  obtain ⟨C, Cpos, hC⟩ := radical_tup_E_le
  refine ⟨log C, fun k ↦ ?_⟩
  apply ENNReal.ofReal_le_ofReal
  rw [maxAbs_tup_E, Nat.cast_pow, Nat.cast_natAbs, cast_abs, log_pow, Nat.cast_ofNat, log_abs]
  apply div_le_div_of_nonneg_left (by positivity)
  · apply log_pos
    have := tup_E_ineq_package k
    rw [← cast_one, cast_lt, one_lt_radical_iff, Finset.natAbs_prod,
      Finset.one_lt_prod_iff_of_one_le fun i _ ↦ by fin_cases i <;> lia]
    exact ⟨3, by simp, by lia⟩
  · have p8 : (E k ^ 8 : ℝ) ≠ 0 := by
      apply pow_ne_zero
      have : 19 ≤ E k := strictMono_E.monotone k.zero_le
      positivity
    rw [show (8 : ℝ) = (8 : ℕ) by rfl, ← log_pow, ← log_mul (by rw [cast_ne_zero]; lia) p8]
    exact log_le_log (mod_cast radical_pos _) (mod_cast hC _)

open Filter in
lemma liminf_tupleQuality_tup_E : 9 / 8 ≤ liminf (tupleQuality ∘ tup ∘ E) atTop := by
  obtain ⟨C, hC⟩ := le_tupleQuality
  apply (liminf_le_liminf (.of_forall hC)).trans_eq'
  have e₁ : (9 / 8 : ENNReal) = ENNReal.ofReal (9 / 8) := by
    simp [ENNReal.ofReal_div_of_pos (show 0 < 8 by simp)]
  rw [e₁]
  refine (ENNReal.tendsto_ofReal ?_).liminf_eq
  let f (k) := log (E k)
  change Tendsto ((fun x ↦ 9 * x / (C + 8 * x)) ∘ f) atTop (nhds (9 / 8))
  have ttf : Tendsto f atTop atTop := by
    refine tendsto_log_atTop.comp (tendsto_intCast_atTop_atTop.comp ?_)
    exact tendsto_atTop_atTop_of_monotone strictMono_E.monotone fun b ↦
      ⟨(b - 19).natAbs, by lia [@add_nineteen_le_E (b - 19).natAbs]⟩
  refine Tendsto.comp ?_ ttf
  apply Tendsto.congr' (f₁ := fun x ↦ 9 / (C * x⁻¹ + 8))
  · exact (eventually_ne_atTop 0).mp (.of_forall fun _ _ ↦ by field)
  · refine tendsto_const_nhds.div ?_ (by simp)
    nth_rw 2 [show 8 = C * 0 + 8 by simp]
    exact (tendsto_inv_atTop_zero.const_mul _).add_const _

end Quality

end FourCase

open FourCase

theorem quality_ramaekersTuples_four_ge : 9 / 8 ≤ quality (ramaekersTuples 4) := by
  refine quality_ge_of_liminf_univ ⟨_, injective_tup_E⟩ ?_ liminf_tupleQuality_tup_E
  simp [tup_E_mem_ramaekersTuples]

theorem not_ramaekersConjecture_four : ¬RamaekersConjecture 4 := by
  refine (quality_ramaekersTuples_four_ge.trans_lt' ?_).ne'
  rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp)]
  norm_num
