import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Redhill.Defs

namespace KonyaginPrelude

variable (k : ℕ)

/-- The quintuple function defined in Section 2.1. -/
def tup : Fin 5 → ℤ
  | 0 => (6 ^ 2 ^ k + 1) ^ 3
  | 1 => -(6 ^ 2 ^ k - 1) ^ 3
  | 2 => -6 * (6 ^ 2 ^ k) ^ 2
  | 3 => -31
  | 4 => 29

lemma sum_tup : ∑ i, tup k i = 0 := by
  simp [tup, Fin.sum_univ_five]
  ring

lemma injective_tup : tup.Injective := fun i j e ↦ by
  replace e : (6 ^ 2 ^ i + 1 : ℤ) ^ 3 = (6 ^ 2 ^ j + 1) ^ 3 := congr($e 0)
  rwa [pow_left_inj₀ (by positivity) (by positivity) (by lia), add_right_cancel_iff,
    pow_right_inj₀ (by lia) (by lia), Nat.pow_right_inj one_lt_two] at e

section Log

open Real UniqueFactorizationMonoid UniqueFactorizationDomain

lemma six_pow_pos {n : ℕ} (hn : n ≠ 0) : 0 < (6 : ℤ) ^ n - 1 := by
  rw [sub_pos]
  exact one_lt_pow₀ (by lia) hn

lemma radical_tup_dvd : radical (∏ i, tup k i) ∣ (6 ^ (2 * 2 ^ k) - 1) * 5394 := by
  simp_rw [show (5394 : ℤ) = 6 * 31 * 29 by lia, ← mul_assoc, tup, Fin.prod_univ_five]
  iterate 3 refine radical_mul_dvd.trans (mul_dvd_mul ?_ ?_)
  · rw [mul_neg, radical_neg, ← mul_pow, ← mul_self_sub_one, ← sq, pow_mul', radical_pow _ (by lia)]
    exact radical_dvd_self
  · rw [neg_mul, radical_neg, ← pow_mul, ← pow_succ', radical_pow _ (by lia)]
    exact radical_dvd_self
  · simp [radical_dvd_self]
  · exact radical_dvd_self

lemma one_lt_radical_tup : 1 < radical (∏ i, tup k i) := by
  simp_rw [Int.one_lt_radical_iff, tup, Fin.prod_univ_five, Int.natAbs_mul, Int.natAbs_neg,
    Int.natAbs_pow, Int.reduceAbs, ← mul_assoc]
  rw [Nat.one_lt_mul_iff]
  simp_rw [show 1 < 29 by lia, or_true, show 0 < 29 by lia, and_true]
  suffices 0 < (6 ^ 2 ^ k - 1 : ℤ).natAbs by positivity
  rw [Int.natAbs_pos]
  exact (six_pow_pos (by positivity)).ne'

lemma log_radical_tup_le : log (radical (∏ i, tup k i) : ℤ) ≤ 2 * 2 ^ k * log 6 + log 5394 := by
  rw [log_le_iff_le_exp (by exact_mod_cast Int.radical_pos),
    exp_add, exp_log (by lia), mul_comm (_ * _), exp_mul, exp_log (by lia)]
  norm_cast
  push_cast
  have : 0 < (6 : ℤ) ^ (2 * 2 ^ k) - 1 := six_pow_pos (by positivity)
  apply (Int.le_of_dvd (by positivity) (radical_tup_dvd k)).trans
  gcongr
  lia

lemma maxAbs_tup : maxAbs (tup k) = (6 ^ 2 ^ k + 1) ^ 3 := by
  simp_rw [maxAbs, List.ofFn_succ, List.ofFn_zero, Fin.reduceSucc, List.foldr_cons, List.foldr_nil]
  change max ((6 ^ 2 ^ k + 1) ^ 3) _ = _
  have e1 : max (tup k 3).natAbs (max (tup k 4).natAbs 0) = 31 := by simp [tup]
  simp_rw [e1, sup_eq_left, tup]
  have e2 : max (-6 * (6 ^ 2 ^ k) ^ 2).natAbs 31 = 6 ^ (2 * 2 ^ k + 1) := by
    rw [neg_mul, Int.natAbs_neg, ← pow_mul', ← pow_succ', Int.natAbs_pow]
    simp_rw [Int.reduceAbs, sup_eq_left]
    apply (show 31 ≤ 6 ^ (2 * 2 ^ 0 + 1) by lia).trans
    gcongr <;> lia
  rw [e2, sup_le_iff, Int.natAbs_neg, Int.natAbs_pow]
  refine ⟨pow_le_pow_left₀ (zero_le _) (by lia) _, ?_⟩
  calc
    _ ≤ 6 ^ (3 * 2 ^ k) := by
      rw [Nat.succ_mul 2]
      gcongr
      · lia
      · exact Nat.one_le_two_pow
    _ ≤ _ := by
      rw [pow_mul']
      gcongr
      exact Nat.le_add_right ..

lemma le_tupleQuality :
    .ofReal ((3 * 2 ^ k * log 6) / (2 * 2 ^ k * log 6 + log 5394)) ≤ tupleQuality (tup k) := by
  apply ENNReal.ofReal_le_ofReal
  rw [maxAbs_tup]
  apply div_le_div₀
  · positivity
  · push_cast
    rw [log_pow, Nat.cast_ofNat, mul_assoc]
    gcongr
    calc
      _ = log (6 ^ 2 ^ k) := by simp
      _ ≤ _ := by
        gcongr
        lia
  · apply log_pos
    exact_mod_cast one_lt_radical_tup k
  · exact log_radical_tup_le k

open Filter in
lemma liminf_tupleQuality_tup : 3 / 2 ≤ liminf (tupleQuality ∘ tup) atTop := by
  refine le_of_eq_of_le ?_ (liminf_le_liminf (.of_forall le_tupleQuality))
  have ceq : (3 / 2 : ENNReal) = ENNReal.ofReal (3 / 2) := by
    simp [ENNReal.ofReal_div_of_pos zero_lt_two]
  simp_rw [ceq, mul_assoc]
  refine (ENNReal.tendsto_ofReal ?_).liminf_eq.symm
  change Tendsto ((fun x ↦ 3 * x / (2 * x + log 5394)) ∘ (2 ^ · * log 6)) atTop (nhds (3 / 2))
  have tt : Tendsto (2 ^ · * log 6) atTop atTop := by
    rw [tendsto_mul_const_atTop_of_pos (by positivity)]
    exact tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  refine Tendsto.comp ?_ tt
  rw [← tendsto_inv_iff₀ (by positivity), show (3 / 2 : ℝ)⁻¹ = 2 / 3 + 0 by norm_num]
  apply Tendsto.congr' (f₁ := fun x ↦ 2 / 3 + log 5394 / 3 * x⁻¹)
  · apply eventually_atTop.mpr -- rw [eventually_atTop] doesn't work
    refine ⟨1, fun x hx ↦ ?_⟩
    simp only [inv_div]
    rw [add_div, mul_div_mul_right _ _ (by positivity), ← div_div, div_eq_mul_inv _ x]
  · exact (Tendsto.const_div_atTop (fun _ ↦ id) _).const_add _

end Log

section Coprime

lemma six_pow_two_pow_mod_29_mem : (6 ^ 2 ^ k : ℤ) % 29 ∈ [6, 7, 20, 23] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, sq, Int.mul_emod]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ih
    obtain ih | ih | ih | ih := ih <;> simp [ih]

lemma six_pow_two_pow_mod_31_mem : (6 ^ 2 ^ k : ℤ) % 31 ∈ [5, 6, 25] := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_mul, sq, Int.mul_emod]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ih
    obtain ih | ih | ih := ih <;> simp [ih]

-- `IsCoprime` subtraction lemmas would be really helpful here!
lemma pairwiseCoprime_tup : PairwiseCoprime (tup k) := fun i j h ↦ by
  unfold tup
  set s : ℤ := 6 ^ 2 ^ k
  have rearr : Multiset.ofList [(s + 1) ^ 3, -(s - 1) ^ 3, -6 * s ^ 2, -31, 29] =
      [29, -31, -6 * s ^ 2, (s + 1) ^ 3, -(s - 1) ^ 3] := by
    rw [Multiset.coe_eq_coe]
    grind
  rw [rearr, Multiset.pairwise_coe_iff_pairwise fun _ _ h ↦ h.symm, List.pairwise_cons]
  have p29 : Prime (29 : ℤ) := by rw [Int.prime_ofNat_iff]; decide
  have p31 : Prime (31 : ℤ) := by rw [Int.prime_ofNat_iff]; decide
  refine ⟨fun a ma ↦ ?_, ?_⟩
  · fin_cases ma
    · decide
    · exact IsCoprime.mul_right (by decide) ((IsCoprime.pow_right (by decide)).pow_right)
    · apply IsCoprime.pow_right
      rw [p29.coprime_iff_not_dvd, Int.dvd_iff_emod_eq_zero, ← Int.emod_add_emod]
      have := six_pow_two_pow_mod_29_mem k
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      obtain h | h | h | h := this <;> norm_num [s, h]
    · refine IsCoprime.neg_right (IsCoprime.pow_right ?_)
      rw [p29.coprime_iff_not_dvd, Int.dvd_iff_emod_eq_zero, ← Int.emod_sub_emod]
      have := six_pow_two_pow_mod_29_mem k
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      obtain h | h | h | h := this <;> norm_num [s, h]
  rw [List.pairwise_cons]
  refine ⟨fun a ma ↦ ?_, ?_⟩
  · apply IsCoprime.neg_left
    fin_cases ma
    · exact IsCoprime.mul_right (by decide) ((IsCoprime.pow_right (by decide)).pow_right)
    · apply IsCoprime.pow_right
      rw [p31.coprime_iff_not_dvd, Int.dvd_iff_emod_eq_zero, ← Int.emod_add_emod]
      have := six_pow_two_pow_mod_31_mem k
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      obtain h | h | h := this <;> norm_num [s, h]
    · refine (IsCoprime.pow_right ?_).neg_right
      rw [p31.coprime_iff_not_dvd, Int.dvd_iff_emod_eq_zero, ← Int.emod_sub_emod]
      have := six_pow_two_pow_mod_31_mem k
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      obtain h | h | h := this <;> norm_num [s, h]
  rw [List.pairwise_cons]
  refine ⟨fun a ma ↦ ?_, ?_⟩
  · simp_rw [neg_mul, IsCoprime.neg_left_iff, s, ← pow_mul, ← pow_succ']
    rw [IsCoprime.pow_left_iff (by positivity)]
    fin_cases ma <;> unfold s
    · apply IsCoprime.pow_right
      rw [show 2 ^ k = 2 ^ k - 1 + 1 by grind, pow_succ, IsCoprime.mul_add_right_right_iff]
      decide
    · refine (IsCoprime.pow_right ?_).neg_right
      rw [show 2 ^ k = 2 ^ k - 1 + 1 by grind, pow_succ, sub_eq_add_neg,
        IsCoprime.mul_add_right_right_iff]
      decide
  rw [List.pairwise_pair, IsCoprime.pow_left_iff zero_lt_three, IsCoprime.neg_right_iff,
    IsCoprime.pow_right_iff zero_lt_three, show s - 1 = 1 * (s + 1) + -2 by ring,
    IsCoprime.mul_add_right_right_iff, IsCoprime.neg_right_iff]
  unfold s
  rw [show 2 ^ k = 2 ^ k - 1 + 1 by grind,
    show (6 : ℤ) ^ (2 ^ k - 1 + 1) = 3 * 6 ^ (2 ^ k - 1) * 2 by ring,
    IsCoprime.mul_add_right_left_iff]
  decide

end Coprime

lemma strongSSC_tup : StrongSSC (tup k) := fun p n h₁ h₂ h₃ ↦ by
  sorry

lemma tup_mem_factorFreeTuples : tup k ∈ factorFreeTuples ∅ 5 := by
  simp [factorFreeTuples, sum_tup, strongSSC_tup, pairwiseCoprime_tup]

end KonyaginPrelude

open KonyaginPrelude

/-- Theorem 2.1. -/
theorem konyagin_prelude : 3 / 2 ≤ quality (factorFreeTuples ∅ 5) := by
  apply quality_ge_of_liminf ⟨_, injective_tup⟩
  · exact Set.range_subset_iff.mpr tup_mem_factorFreeTuples
  · exact liminf_tupleQuality_tup
