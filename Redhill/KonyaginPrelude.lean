import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Redhill.Defs

namespace KonyaginPrelude

variable (k : ℕ)

/-- The quintuple function defined in Section 2.1. -/
def tup : Multiset ℤ :=
  .ofList [(6 ^ 2 ^ k + 1) ^ 3, -(6 ^ 2 ^ k - 1) ^ 3, -6 * (6 ^ 2 ^ k) ^ 2, -31, 29]

lemma natAbs_6pa1 {n : ℕ} : (6 ^ n + 1 : ℤ).natAbs = 6 ^ n + 1 := by
  rw [Int.natAbs_add_of_nonneg (by positivity) zero_le_one]
  simp

lemma natAbs_6ps1 {n : ℕ} : (6 ^ n - 1 : ℤ).natAbs = 6 ^ n - 1 := by
  rw [Int.natAbs_sub_of_nonneg_of_le zero_le_one (one_le_pow₀ (by norm_num))]
  simp

lemma six_pow_two_pow_sub_one_pos : 0 < 6 ^ 2 ^ k - 1 :=
  Nat.zero_lt_sub_of_lt (Nat.one_lt_pow (by positivity) (by lia))

lemma card_tup : (tup k).card = 5 := by
  simp [tup]

lemma sum_tup : (tup k).sum = 0 := by
  simp [tup]
  ring

lemma injective_tup : tup.Injective := fun i j e ↦ by
  have w : -6 * (6 ^ 2 ^ i) ^ 2 ∈ tup i := by simp [tup]
  rw [e] at w
  simp_rw [tup, Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at w
  have ev : Even (-6 * (6 ^ 2 ^ i) ^ 2) := by
    apply Even.mul_right
    decide
  have e6 : Even (6 : ℤ) := by decide
  obtain w | w | w | w | w := w <;> rw [w] at ev
  · rw [Int.even_pow, Int.even_add_one, Int.even_pow] at ev
    simp [e6] at ev
  · rw [even_neg, Int.even_pow, Int.even_sub_one, Int.even_pow] at ev
    simp [e6] at ev
  on_goal 2 => lia
  on_goal 2 => lia
  rw [mul_right_inj' (by lia), sq_eq_sq₀ (by positivity) (by positivity)] at w
  replace w := Int.pow_right_injective (by lia) w
  rwa [Nat.pow_right_inj one_lt_two] at w

section Log

open Real

lemma radical_tup_dvd : (tup k).prod.natAbs.radical ∣ (6 ^ (2 * 2 ^ k) - 1) * 6 * 31 * 29 := by
  simp_rw [tup, Multiset.prod_coe, List.prod_cons, List.prod_nil, mul_one, ← mul_assoc]
  rw [mul_neg (_ ^ 3), ← mul_pow, ← mul_self_sub_one, ← sq, ← pow_mul']
  simp_rw [Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_pow, natAbs_6ps1, Int.reduceAbs]
  iterate 2 refine Nat.radical_mul_dvd.trans (mul_dvd_mul ?_ Nat.radical_dvd_self)
  rw [mul_assoc, ← pow_succ' 6]
  refine Nat.radical_mul_dvd.trans (mul_dvd_mul ?_ ?_)
  all_goals
    rw [Nat.radical_pow (by positivity)]
    exact Nat.radical_dvd_self

lemma one_lt_radical_tup : 1 < (tup k).prod.natAbs.radical := by
  rw [Nat.one_lt_natRadical_iff, prod_natAbs_comm, tup]
  simp_rw [Multiset.map_coe, List.map_cons, List.map_nil, Int.natAbs_mul, Int.natAbs_neg,
    Int.natAbs_pow, Int.reduceAbs, Multiset.prod_coe, List.prod_cons, List.prod_nil, mul_one,
    Nat.reduceMul, ← mul_assoc]
  rw [Nat.one_lt_mul_iff]
  norm_num
  constructor
  · positivity
  · rw [natAbs_6ps1]
    positivity [six_pow_two_pow_sub_one_pos k]

lemma log_radical_tup_le : log (tup k).prod.natAbs.radical ≤ 2 * 2 ^ k * log 6 + log 5394 := by
  have n₁ : 1 < (6 : ℝ) ^ (2 * 2 ^ k) := by
    exact one_lt_pow₀ (by norm_num) (by positivity)
  have n₂ : (6 : ℝ) ^ (2 * 2 ^ k) - 1 ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact n₁.ne
  calc
    _ ≤ log ((6 ^ (2 * 2 ^ k) - 1) * 6 * 31 * 29) := by
      gcongr
      · exact_mod_cast Nat.natRadical_pos
      have rhs_pos : 0 < (6 ^ (2 * 2 ^ k) - 1) * 6 * 31 * 29 := by
        iterate 3 refine Nat.mul_pos ?_ (by decide)
        exact Nat.zero_lt_sub_of_lt (Nat.one_lt_pow (by positivity) (by decide))
      have lhs_pos := Nat.pos_of_dvd_of_pos (radical_tup_dvd k) rhs_pos
      have llr := Nat.le_of_dvd rhs_pos (radical_tup_dvd k)
      rw [← Nat.cast_le (α := ℝ)] at llr
      push_cast at llr
      convert llr
      rw [Nat.cast_sub (by rw [Order.one_le_iff_pos]; positivity)] at llr
      simp
    _ ≤ _ := by
      simp_rw [mul_assoc]
      norm_num
      rw [log_mul n₂ (by norm_num), ← mul_assoc]
      refine add_le_add_left ?_ _
      rw [show (2 * 2 ^ k : ℝ) = (2 * 2 ^ k : ℕ) by norm_cast, ← log_pow]
      gcongr
      · rwa [sub_pos]
      · exact (sub_one_lt _).le

lemma maxAbs_tup : maxAbs (tup k) = (6 ^ 2 ^ k + 1) ^ 3 := by
  simp_rw [tup, maxAbs, Multiset.map_coe, Multiset.coe_fold_r, List.map_cons, List.map_nil,
    Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_pow, natAbs_6pa1, natAbs_6ps1, Int.reduceAbs,
    List.foldr_cons, List.foldr_nil, show max 31 (max 29 0) = 31 by norm_num]
  simp only [sup_eq_left, sup_le_iff]
  have : 1 ≤ 6 := by simp
  refine ⟨?_, ?_, ?_⟩
  · gcongr
    lia
  · rw [← pow_mul', ← pow_succ']
    calc
      _ ≤ 6 ^ (3 * 2 ^ k) := by
        rw [Nat.succ_mul 2]
        gcongr
        · norm_num
        · exact Nat.one_le_two_pow
      _ ≤ _ := by
        rw [pow_mul']
        gcongr
        exact Nat.le_add_right ..
  · trans (6 ^ 2 ^ 0 + 1) ^ 3
    · norm_num
    · gcongr <;> lia

lemma le_multisetQuality :
    .ofReal ((3 * 2 ^ k * log 6) / (2 * 2 ^ k * log 6 + log 5394)) ≤ multisetQuality (tup k) := by
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
lemma liminf_multisetQuality_tup : 3 / 2 ≤ liminf (multisetQuality ∘ tup) atTop := by
  refine le_of_eq_of_le ?_ (liminf_le_liminf (.of_forall le_multisetQuality))
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
lemma pairwise_tup_isCoprime : (tup k).Pairwise IsCoprime := by
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

lemma strongSSC_tup : StrongSSC (tup k) := fun p n h₁ h₂ ↦ by
  unfold tup at h₁
  set s : ℤ := 6 ^ 2 ^ k
  sorry

lemma tup_mem_factorFreeMultisets : tup k ∈ factorFreeMultisets ∅ 5 := by
  simp [factorFreeMultisets, card_tup, sum_tup, strongSSC_tup, pairwise_tup_isCoprime]

end KonyaginPrelude

open KonyaginPrelude

/-- Theorem 2.1. -/
theorem konyagin_prelude : 3 / 2 ≤ quality (factorFreeMultisets ∅ 5) := by
  apply quality_ge_of_liminf ⟨_, injective_tup⟩
  · exact Set.range_subset_iff.mpr tup_mem_factorFreeMultisets
  · exact liminf_multisetQuality_tup
