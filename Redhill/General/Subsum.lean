module

public import Redhill.Common.SubsumCondition
public import Redhill.General.Defs

namespace GeneralCase

open Fin Finset Nat

variable {n : ℕ} {F : Finset ℕ} {h : ℕ}

/-- The embedding for the first subsum block reduction. -/
def redEmb1 : Fin 4 ↪ Fin (n + 6) :=
  ⟨fun i ↦ (i.natAdd 2).natAdd n, fun i j h ↦ by simpa [natAdd_inj 2] using h⟩

variable (n F) in
/-- The sum of `tup n F h`'s first `n + 2` elements, not depending on `h`. -/
def tailK : ℕ := (VW n F).v + (VW n F).w + ∑ i ∈ range n, primeChain (200 * Y F ^ 6) i

lemma sum_redEmb1_compl : ∑ i ∉ univ.map redEmb1, (tup n F h i).natAbs = tailK n F := by
  have cnn (i : Fin n) (j : Fin 6) : castAdd 6 i ≠ natAdd n j := ne_of_lt (by grind)
  have s₁ : univ.map (@castAddEmb n 6) ⊆ (univ.map redEmb1)ᶜ := fun i mi ↦ by
    simp_rw [mem_map, mem_univ, true_and, coe_castAddEmb] at mi
    obtain ⟨j, rfl⟩ := mi
    simp_rw [redEmb1, mem_compl, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk,
      not_exists]
    grind
  simp_rw [← sum_sdiff s₁, sum_map, castAddEmb_apply, tup_castAdd, Int.natAbs_natCast]
  have s₂ : (univ.map redEmb1)ᶜ \ univ.map (castAddEmb 6) = {natAdd n 0, natAdd n 1} := by
    ext i
    simp_rw [mem_sdiff, mem_compl, mem_map, mem_univ, true_and, castAddEmb_apply, not_exists]
    cases i using addCases with
    | left i => grind [castAdd_inj]
    | right j =>
      simp_rw [cnn, not_false_eq_true, implies_true, and_true, redEmb1, Function.Embedding.coeFn_mk,
        mem_insert, mem_singleton, natAdd_inj]
      decide +revert
  rw [s₂, sum_pair (by grind), tup_natAdd_zero, tup_natAdd_one, Int.natAbs_natCast,
    Int.natAbs_neg, Int.natAbs_natCast, sum_univ_eq_sum_range, tailK]

lemma X_le_natAbs_redEmb1
    {b₁ b₂ b₃ b₄ : SignType} (hb : b₁ ≠ b₂ ∨ b₂ ≠ b₃ ∨ b₃ ≠ b₄) (hh : tailK n F < X F h) :
    X F h ≤ (b₁ * (X F h ^ 2 + 10 * Y F ^ 3 : ℤ) ^ 2 + b₂ * ((10 * Y F - 1) * X F h ^ 4) +
      b₃ * (X F h - Y F) ^ 5 + b₄ * -(X F h + Y F) ^ 5).natAbs := by
  sorry

lemma eventually_X_gt (K : Finset ℕ → ℕ) : ∀ᶠ h in Filter.atTop, K F < X F h := by
  rw [Filter.eventually_atTop]
  obtain ⟨n, hn⟩ : ∃ n, K F < (Y F + 1) ^ n := add_one_pow_unbounded_of_pos _ (by grind [Y_pos])
  refine ⟨n, fun h hh ↦ hn.trans_le ?_⟩
  exact Nat.pow_le_pow_right (zero_lt_succ _) (hh.trans (self_le_factorial _))

lemma isSubsumBlock_redEmb1 :
    ∀ᶠ h in Filter.atTop, IsSubsumBlock (tup n F h) (univ.map redEmb1) := by
  refine (eventually_X_gt (F := F) (tailK n)).mono fun h hh ↦
    IsSubsumBlock.of_sum_natAbs_lt redEmb1 fun b ncb ↦ ?_
  conv_rhs => rw [redEmb1, sum_univ_four]
  simp only [Function.Embedding.coeFn_mk, reduceNatAdd, sum_redEmb1_compl,
    tup_natAdd_two, tup_natAdd_three, tup_natAdd_four, tup_natAdd_five]
  apply hh.trans_le
  suffices ∀ {b₁ b₂ b₃ b₄ : SignType}, b₁ ≠ b₂ ∨ b₂ ≠ b₃ ∨ b₃ ≠ b₄ →
      X F h ≤ (b₁ * (X F h ^ 2 + 10 * Y F ^ 3 : ℤ) ^ 2 + b₂ * ((10 * Y F - 1) * X F h ^ 4) +
        b₃ * (X F h - Y F) ^ 5 + b₄ * -(X F h + Y F) ^ 5).natAbs by
    apply this
    contrapose! ncb
    exact ⟨b 0, fun i ↦ by fin_cases i <;> lia⟩
  exact fun hb ↦ X_le_natAbs_redEmb1 hb hh

public theorem strongSSC_tup : ∀ᶠ h in Filter.atTop, StrongSSC (tup n F h) := by
  sorry

end GeneralCase
