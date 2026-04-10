module

public import Redhill.General.Coprime
public import Redhill.General.Subsum
public import Redhill.Common.Conjectures

@[expose] public section

namespace GeneralCase

open Filter

variable {n : ℕ} {F : Finset ℕ}

lemma tup_mem_factorFreeTuples (hF : ∀ f ∈ F, 3 ≤ f) :
    ∀ᶠ h in atTop, tup n F h ∈ factorFreeTuples F (n + 6) := by
  simp_rw [factorFreeTuples, Set.mem_setOf_eq, eventually_and]
  exact ⟨.of_forall fun h ↦ sum_tup, strongSSC_tup, pairwiseCoprime_tup,
    .of_forall fun h f mf ↦ not_dvd_tup mf (hF f mf)⟩

end GeneralCase

open GeneralCase

theorem quality_factorFreeTuples_Icc_ge {n l : ℕ} (hn : 6 ≤ n) (hl : 11 ≤ l) :
    5 / 4 ≤ quality (factorFreeTuples (Finset.Icc 3 l) n) := by
  sorry

/-- Theorem 1.14. -/
theorem quality_factorFreeTuples_ge {n : ℕ} {F : Finset ℕ} (hn : 6 ≤ n) (hF : ∀ f ∈ F, 3 ≤ f) :
    5 / 4 ≤ quality (factorFreeTuples F n) := by
  refine (quality_factorFreeTuples_Icc_ge (l := max 11 (F.sup id)) hn (le_max_left ..)).trans
    (quality_factorFreeTuples_anti fun f mf ↦ ?_)
  rw [Finset.mem_Icc, le_max_iff]
  exact ⟨hF _ mf, .inr (Finset.le_sup (f := id) mf)⟩

theorem not_ramaekersConjecture_ge_six {n : ℕ} (hn : 6 ≤ n) : ¬RamaekersConjecture n := by
  have := quality_factorFreeTuples_ge (F := ∅) hn (by simp)
    |>.trans quality_factorFreeTuples_le_ramaekersTuples
  refine (this.trans_lt' ?_).ne'
  rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp)]
  norm_num
