module

public import Redhill.Common.SubsumCondition
public import Redhill.Odd.Defs
public import Redhill.ToMathlib.NatSumProd

@[expose] public section

namespace OddCase

open Fin Finset

variable {n : ℕ} {F : Finset ℕ} {x : ℤ} (dx : ↑(Y n F) ∣ x) (nzx : x ≠ 0) (nF : 0 ∉ F)

/-- The embedding for the first subsum block reduction. -/
def redEmb1 : Fin 3 ↪ Fin (n + 5) :=
  ⟨fun i ↦ (i.natAdd 2).natAdd n, fun i j h ↦ by simpa [Fin.natAdd_inj 2] using h⟩

lemma U_lt_V : U n F < (VW n F).v :=
  calc
    _ ≤ max (U n F) (F.sup id) := le_max_left ..
    _ ≤ _ := Nat.le_primorial_self
    _ < _ := (VW n F).ineq_chain.1

lemma U_lt_W : U n F < (VW n F).w :=
  U_lt_V.trans_le (VW n F).ineq_chain.2.1

lemma sum_redEmb1_compl :
    ∑ i ∈ (univ.map redEmb1)ᶜ, (tup n F x i).natAbs =
    (VW n F).v + (VW n F).w + ∑ i ∈ range n, primeChain (max 16 (F.sup id)) i := by
  have cnn (i : Fin n) (j : Fin 5) : castAdd 5 i ≠ natAdd n j := ne_of_lt (by grind)
  have s₁ : univ.map (@castAddEmb n 5) ⊆ (univ.map redEmb1)ᶜ := fun i mi ↦ by
    simp_rw [mem_map, mem_univ, true_and, coe_castAddEmb] at mi
    obtain ⟨j, rfl⟩ := mi
    simp_rw [redEmb1, mem_compl, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk,
      not_exists]
    grind
  simp_rw [← sum_sdiff s₁, sum_map, castAddEmb_apply, tup_castAdd, Int.natAbs_natCast]
  have s₂ : (univ.map redEmb1)ᶜ \ univ.map (castAddEmb 5) = {natAdd n 0, natAdd n 1} := by
    ext i
    simp_rw [mem_sdiff, mem_compl, mem_map, mem_univ, true_and, castAddEmb_apply, not_exists]
    cases i using Fin.addCases with
    | left i => grind [castAdd_inj]
    | right j =>
      simp_rw [cnn, not_false_eq_true, implies_true, and_true, redEmb1, Function.Embedding.coeFn_mk,
        mem_insert, mem_singleton, natAdd_inj]
      decide +revert
  rw [s₂, sum_pair (by grind), tup_natAdd_zero, tup_natAdd_one, Int.natAbs_natCast,
    Int.natAbs_neg, Int.natAbs_natCast, sum_univ_eq_sum_range]

include nF in
lemma sum_redEmb1_compl_lt : ∑ i ∈ (univ.map redEmb1)ᶜ, (tup n F x i).natAbs < Y n F := by
  rw [sum_redEmb1_compl]
  calc
    _ ≤ (VW n F).v + (VW n F).w + ∏ i ∈ range n, primeChain (max 16 (F.sup id)) i :=
      add_le_add_right (Nat.sum_le_prod (by grind [sixteen_lt_primeChain])) _
    _ < (VW n F).v * (VW n F).w * ∏ i ∈ range n, primeChain (max 16 (F.sup id)) i := by
      apply Nat.add3_lt_mul3
      · grind [U, U_lt_V]
      · grind [U, U_lt_W]
      · exact one_le_prod (by grind [sixteen_lt_primeChain])
    _ ≤ _ := by
      unfold Y
      set P := ∏ i ∈ range n, primeChain (max 16 (F.sup id)) i
      calc
        _ = 1 * (P * (VW n F).v * (VW n F).w) := by ring
        _ ≤ 10 * F.prod id * (P * (VW n F).v * (VW n F).w) := by
          gcongr
          suffices 0 < F.prod id by lia
          exact prod_pos (by grind)
        _ = _ := by ring

include dx nzx nF in
lemma Y_le_natAbs_redEmb1 {b₁ b₂ b₃ : SignType} (h : b₁ ≠ b₂ ∨ b₁ ≠ b₃) :
    Y n F ≤ (b₁ * (x - 1) ^ 5 + b₂ * (10 * (x ^ 2 + 1) ^ 2) - b₃ * (x + 1) ^ 5).natAbs := by
  sorry

include dx nzx nF in
lemma isSubsumBlock_redEmb1 :
    IsSubsumBlock (tup n F x) (univ.map redEmb1) := by
  refine IsSubsumBlock.of_sum_natAbs_lt redEmb1 fun b ncb ↦ ?_
  conv_rhs => rw [redEmb1, sum_univ_three]
  simp only [Function.Embedding.coeFn_mk, reduceNatAdd,
    tup_natAdd_two, tup_natAdd_three, tup_natAdd_four, mul_neg, ← sub_eq_add_neg]
  apply (sum_redEmb1_compl_lt nF).trans_le
  suffices ∀ {b₁ b₂ b₃ : SignType}, b₁ ≠ b₂ ∨ b₁ ≠ b₃ →
      Y n F ≤ (b₁ * (x - 1) ^ 5 + b₂ * (10 * (x ^ 2 + 1) ^ 2) - b₃ * (x + 1) ^ 5).natAbs by
    apply this
    contrapose! ncb
    exact ⟨b 0, fun i ↦ by fin_cases i <;> tauto⟩
  exact Y_le_natAbs_redEmb1 dx nzx nF

include dx nzx nF in
lemma strongSSC_tup : StrongSSC (tup n F x) := by
  sorry

end OddCase
