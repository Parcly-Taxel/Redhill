module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Redhill.Common.Conjectures
public import Redhill.General.Coprime
public import Redhill.General.Subsum

@[expose] public section

namespace GeneralCase

open Filter UniqueFactorizationMonoid

variable {n : ℕ} {F : Finset ℕ}

lemma tup_mem_factorFreeTuples (hF : ∀ f ∈ F, 3 ≤ f) :
    ∀ᶠ h in atTop, tup n F h ∈ factorFreeTuples F (n + 6) := by
  simp_rw [factorFreeTuples, Set.mem_setOf_eq, eventually_and]
  exact ⟨.of_forall fun h ↦ sum_tup, strongSSC_tup, pairwiseCoprime_tup,
    .of_forall fun h f mf ↦ not_dvd_tup mf (hF f mf)⟩

open Polynomial in
lemma radical_tup_dvd :
    ∃ P : ℤ[X], P.degree = 4 ∧ ∀ h, radical (∏ i, tup n F h i) ∣ P.eval (X F h) := by
  simp_rw [Fin.prod_univ_add, tup_castAdd, Fin.prod_univ_six, tup_natAdd_zero,
    tup_natAdd_one, tup_natAdd_two, tup_natAdd_three, tup_natAdd_four, tup_natAdd_five,
    ← mul_assoc, mul_neg, neg_mul, neg_neg, ← Nat.cast_prod, ← Nat.cast_mul]
  set C := (∏ i : Fin n, primeChain (200 * Y F ^ 6) i.1) * (VW n F).v * (VW n F).w
  have Cpos : 0 < C := by
    iterate 2 refine Nat.mul_pos ?_ (by grind [(VW n F).m_lt_v, (VW n F).v_le_w])
    exact Finset.prod_pos fun i _ ↦ by grind [primeChain_gt]
  let x : ℤ[X] := Polynomial.X
  refine ⟨C * (10 * Y F - 1) * (Y F + 1) * (x ^ 2 + 10 * Y F ^ 3) * (x - Y F) * (x + Y F),
    ?_, fun h ↦ ?_⟩
  · iterate 3 rw [degree_mul]
    have d₁ : (Polynomial.C (C * (10 * Y F - 1) * (Y F + 1) : ℤ)).degree = 0 := by
      refine degree_C (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) <;> lia
    simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_ofNat,
      Int.cast_one, Int.cast_add] at d₁
    have d₂ : (x ^ 2 + 10 * Y F ^ 3).degree = 2 := by
      compute_degree
      · simp only [natDegree_X, mul_one, monic_X, Monic.leadingCoeff, one_pow, ne_eq,
          ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not, x]
        decide
      · simp only [natDegree_X, mul_one, x]
        decide
      · decide
      · simp [x]
    have d₃ : (x - Y F).degree = 1 := by compute_degree <;> simp [x]
    have d₄ : (x + Y F).degree = 1 := by compute_degree <;> simp [x]
    rw [d₁, d₂, d₃, d₄]
    decide
  · unfold x
    simp only [eval_mul, eval_natCast, eval_sub, eval_ofNat, eval_one, eval_add, eval_pow, eval_X]
    iterate 2 rw [mul_right_comm _ (_ ^ 2)]
    iterate 3 refine radical_mul_dvd.trans (mul_dvd_mul ?_ (radical_pow_dvd.trans radical_dvd_self))
    refine radical_mul_dvd.trans (mul_dvd_mul radical_dvd_self ?_)
    rw [X, Nat.cast_pow, ← pow_mul, Nat.cast_add_one]
    exact radical_pow_dvd.trans radical_dvd_self

lemma tendsto_X_atTop_atTop : Tendsto (X F) atTop atTop :=
  tendsto_atTop.mpr fun B ↦ (eventually_X_gt fun _ ↦ B).mono fun _ ↦ Nat.le_of_succ_le

lemma radical_tup_le : ∃ C > 0, ∀ᶠ h in atTop, radical (∏ i, tup n F h i) ≤ C * X F h ^ 4 := by
  obtain ⟨P, dP, hP⟩ := @radical_tup_dvd n F
  have nP : P ≠ 0 := by
    rw [← Polynomial.zero_le_degree_iff, dP]
    exact zero_le_four
  have key := P.isEquivalent_cobounded_leading_monomial
  have enr := P.eventually_cofinite_not_isRoot nP
  have tX : Tendsto (fun h ↦ (X F h : ℤ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_X_atTop_atTop
  rw [Int.cobounded_eq] at key
  rw [Int.cofinite_eq] at enr
  replace key : (fun h ↦ P.eval (X F h : ℤ)) =O[atTop] fun h ↦ _ * _ ^ _ :=
    ((key.mono le_sup_right).comp_tendsto tX).isBigO
  replace enr : ∀ᶠ h in atTop, ¬P.IsRoot (X F h) := tX.eventually (enr.filter_mono le_sup_right)
  rw [Asymptotics.isBigO_iff'] at key
  obtain ⟨R, Rpos, hR⟩ := key
  refine ⟨⌈R⌉ * |P.leadingCoeff|, ?_, (enr.and hR).mono fun h ⟨hh₁, hh₂⟩ ↦ ?_⟩
  · apply Int.mul_pos (Int.ceil_pos.mpr Rpos)
    rwa [abs_pos, P.leadingCoeff_ne_zero]
  · apply (Int.le_abs_of_dvd hh₁ (hP h)).trans
    simp_rw [Int.norm_eq_abs, Int.cast_mul, abs_mul, Int.cast_pow, Int.cast_natCast, abs_pow,
      Nat.abs_cast, ← Int.cast_abs, Polynomial.natDegree_eq_of_degree_eq_some dP] at hh₂
    simp_rw [← Int.cast_le (R := ℝ), Int.cast_mul, Int.cast_pow, Int.cast_natCast, mul_assoc]
    exact hh₂.trans (mul_le_mul_of_nonneg_right (Int.le_ceil R) (by positivity))

lemma le_tupleQuality : ∃ C, ∀ᶠ h in atTop,
    .ofReal (5 * Real.log (X F h) / (C + 4 * Real.log (X F h))) ≤ tupleQuality (tup n F h) := by
  obtain ⟨C, Cpos, hC⟩ := @radical_tup_le n F
  refine ⟨Real.log C,
    (hC.and ((@maxAbs_tup n F).and (@strongSSC_tup n F))).mono fun h ⟨hrad, hma, hssc⟩ ↦ ?_⟩
  apply ENNReal.ofReal_le_ofReal
  rw [hma]
  apply div_le_div₀
  · positivity
  · rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, mul_le_mul_iff_right₀ (by simp)]
    exact Real.log_le_log (by grind [Nat.cast_pos, Y_lt_X]) (mod_cast Nat.le_add_right ..)
  · apply Real.log_pos
    rw [← Int.cast_one, Int.cast_lt, Int.one_lt_radical_iff]
    exact hssc.one_lt_natAbs_prod (by lia)
  · rw [show (4 : ℝ) = (4 : ℕ) by rfl, ← Real.log_pow,
      ← Real.log_mul (mod_cast Cpos.ne') (mod_cast pow_ne_zero 4 (by grind [Y_lt_X]))]
    exact Real.log_le_log (mod_cast Int.radical_pos _) (mod_cast hrad)

lemma liminf_tupleQuality_tup : 5 / 4 ≤ liminf (tupleQuality ∘ tup n F) atTop := by
  obtain ⟨C, hC⟩ := @le_tupleQuality n F
  refine le_of_eq_of_le ?_ (liminf_le_liminf hC)
  have e₁ : (5 / 4 : ENNReal) = ENNReal.ofReal (5 / 4) := by
    simp [ENNReal.ofReal_div_of_pos zero_lt_four]
  rw [e₁]
  refine (ENNReal.tendsto_ofReal ?_).liminf_eq.symm
  let f (h : ℕ) := Real.log (X F h)
  change Tendsto ((fun x ↦ 5 * x / (C + 4 * x)) ∘ f) atTop (nhds (5 / 4))
  have ttf : Tendsto f atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_X_atTop_atTop)
  refine Tendsto.comp ?_ ttf
  apply Tendsto.congr' (f₁ := fun x ↦ 5 / (C * x⁻¹ + 4))
  · exact (eventually_ne_atTop 0).mp (.of_forall fun _ _ ↦ by field)
  · refine tendsto_const_nhds.div ?_ four_ne_zero
    nth_rw 2 [show 4 = C * 0 + 4 by simp]
    exact (tendsto_inv_atTop_zero.const_mul _).add_const _

end GeneralCase

open GeneralCase

/-- Theorem 1.14. -/
theorem quality_factorFreeTuples_ge {n : ℕ} {F : Finset ℕ} (hn : 6 ≤ n) (hF : ∀ f ∈ F, 3 ≤ f) :
    5 / 4 ≤ quality (factorFreeTuples F n) := by
  rw [le_iff_exists_add'] at hn
  obtain ⟨n, rfl⟩ := hn
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (tup_mem_factorFreeTuples (n := n) hF)
  refine quality_ge_of_liminf _ _ (Set.Ici_infinite (N₀ + 1))
    (fun i mi j mj e ↦ ?_) (fun h (hh : N₀ < h) ↦ hN₀ h hh.le) liminf_tupleQuality_tup
  replace e := congr($e (Fin.natAdd n 5))
  simp_rw [tup_natAdd_five, neg_inj] at e
  norm_cast at e
  rw [pow_left_inj (by decide), add_left_inj, X, X, Nat.pow_right_inj (by grind [Y_pos])] at e
  grind [Nat.factorial_inj']

theorem not_ramaekersConjecture_ge_six {n : ℕ} (hn : 6 ≤ n) : ¬RamaekersConjecture n := by
  have := quality_factorFreeTuples_ge (F := ∅) hn (by simp)
    |>.trans quality_factorFreeTuples_le_ramaekersTuples
  refine (this.trans_lt' ?_).ne'
  rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp)]
  norm_num
