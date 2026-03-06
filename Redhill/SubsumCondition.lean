import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.Zify

open Finset

variable {n : ℕ} (a : Fin n → ℤ)

/-- The subsum condition: any subset of the tuple summing to 0
is either empty or the whole tuple. -/
def SSC : Prop :=
  ∀ b, b.Nonempty → bᶜ.Nonempty → ∑ i ∈ b, a i ≠ 0

/-- The stronger subsum condition: two disjoint sub-tuples with the same sum
must have their union either empty or the whole tuple. -/
def StrongSSC : Prop :=
  ∀ b c, Disjoint b c → (b ∪ c).Nonempty → (b ∪ c)ᶜ.Nonempty → ∑ i ∈ b, a i ≠ ∑ i ∈ c, a i

/-- Two indices form a subsum pair for `a` if for any disjoint pair of index sets with equal sum,
either both indices are among the index sets or neither are. -/
def SubsumPairFor (i j : Fin n) : Prop :=
  ∀ b c, Disjoint b c → ∑ i ∈ b, a i = ∑ i ∈ c, a i → (i ∈ b ∪ c ↔ j ∈ b ∪ c)

variable {a}

lemma SSC_of_strongSSC (h : StrongSSC a) : SSC a := by
  unfold SSC StrongSSC at *
  contrapose! h
  obtain ⟨b, neb, necb, nzb⟩ := h
  exact ⟨b, ∅, disjoint_empty_right b, by simp [neb], by simp [necb, nzb]⟩

lemma zero_notMem_of_SSC (hn : 2 ≤ n) (hs : ∑ i, a i = 0) (ha : SSC a) : 0 ∉ univ.image a := by
  unfold SSC at ha
  contrapose! ha
  simp only [mem_image, mem_univ, true_and] at ha
  obtain ⟨i, hi⟩ := ha
  refine ⟨{i}ᶜ, ?_, by simp, ?_⟩
  · rw [← card_pos, card_compl, Fintype.card_fin, card_singleton]
    exact Nat.zero_lt_sub_of_lt hn
  · rw [← hs, ← sum_add_sum_compl {i}, sum_singleton, hi, zero_add]

lemma zero_notMem_of_strongSSC
    (hn : 2 ≤ n) (hs : ∑ i, a i = 0) (ha : StrongSSC a) : 0 ∉ univ.image a :=
  zero_notMem_of_SSC hn hs (SSC_of_strongSSC ha)

lemma subsumPairFor_iff_sum_natAbs_lt_aux {i j : Fin n}
    (hi : ∑ k ∈ {i, j}ᶜ, (a k).natAbs < (a i).natAbs)
    {b c : Finset (Fin n)} (dj : Disjoint b c) (hs : ∑ i ∈ b, a i = ∑ i ∈ c, a i) (mi : i ∈ b ∪ c) :
    j ∈ b ∪ c := by
  wlog mi' : i ∈ b generalizing b c
  · rw [union_comm] at mi ⊢
    apply this dj.symm hs.symm mi
    rw [mem_union] at mi
    exact mi.resolve_right mi'
  rw [← insert_erase mi', sum_insert (notMem_erase _ _), ← eq_sub_iff_add_eq] at hs
  apply_fun Int.natAbs at hs
  contrapose! hs
  apply ne_of_gt
  calc
    _ ≤ _ := Int.natAbs_sub_le ..
    _ ≤ ∑ i ∈ c, (a i).natAbs + ∑ i ∈ b.erase i, (a i).natAbs := by
      zify
      gcongr <;> exact abs_sum_le_sum_abs ..
    _ ≤ _ := by
      rw [← sum_union (dj.symm.mono_right (erase_subset _ _))]
      apply sum_le_sum_of_subset
      simp_rw [subset_compl_comm, insert_eq, union_subset_iff, singleton_subset_iff]
      simp only [compl_union, compl_erase, mem_inter, mem_compl, mem_insert, true_or, and_true]
      rw [notMem_union] at hs
      exact ⟨dj.notMem_of_mem_left_finset mi', hs.2, .inr hs.1⟩
    _ < _ := hi

lemma subsumPairFor_iff_sum_natAbs_lt {i j : Fin n}
    (hi : ∑ k ∈ {i, j}ᶜ, (a k).natAbs < (a i).natAbs)
    (hj : ∑ k ∈ {i, j}ᶜ, (a k).natAbs < (a j).natAbs) : SubsumPairFor a i j := fun b c dj hs ↦ by
  rw [pair_comm] at hj
  exact Iff.intro (subsumPairFor_iff_sum_natAbs_lt_aux hi dj hs)
    (subsumPairFor_iff_sum_natAbs_lt_aux hj dj hs)
