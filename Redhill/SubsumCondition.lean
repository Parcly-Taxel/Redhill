import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Zify
import Redhill.ToMathlib.Int

open Finset

variable {n : ℕ} (a : Fin n → ℤ)

/-- The subsum condition: any subset of the tuple summing to 0
is either empty or the whole tuple. -/
def SSC : Prop :=
  ∀ b, b.Nonempty → bᶜ.Nonempty → ∑ i ∈ b, a i ≠ 0

/-- The strong subsum condition: two disjoint sub-tuples with the same sum
must have their union either empty or the whole tuple. -/
def StrongSSC : Prop :=
  ∀ b c, Disjoint b c → (b ∪ c).Nonempty → (b ∪ c)ᶜ.Nonempty → ∑ i ∈ b, a i ≠ ∑ i ∈ c, a i

/-- A subsum block for `a` is an index set respecting the boundaries of any disjoint pair
of index sets with equal sum. -/
def IsSubsumBlock (s : Finset (Fin n)) : Prop :=
  ∀ b c, Disjoint b c → ∑ i ∈ b, a i = ∑ i ∈ c, a i → (s ⊆ b ∨ s ⊆ c ∨ Disjoint s (b ∪ c))

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

namespace IsSubsumBlock

variable {i j : Fin n} {s t : Finset (Fin n)}

lemma empty : IsSubsumBlock a ∅ := fun b c dj h ↦ by simp

lemma singleton : IsSubsumBlock a {i} := fun b c dj h ↦ by simp; grind

lemma subset (hs : IsSubsumBlock a s) (ht : t ⊆ s) : IsSubsumBlock a t := fun b c dj h ↦ by
  specialize hs _ _ dj h
  obtain hs | hs | hs := hs
  · exact .inl (ht.trans hs)
  · exact .inr (.inl (ht.trans hs))
  · exact .inr (.inr (hs.mono_left ht))

lemma union (hs : IsSubsumBlock a s) (ht : IsSubsumBlock a t) (hd : ¬Disjoint s t) :
    IsSubsumBlock a (s ∪ t) := fun b c dj h ↦ by
  specialize hs _ _ dj h
  specialize ht _ _ dj h
  obtain ⟨i, mis, mit⟩ := not_disjoint_iff.mp hd
  obtain hs | hs | hs := hs
  · refine .inl (union_subset hs ?_)
    have : ¬Disjoint t (b ∪ c) := not_disjoint_iff.mpr ⟨i, mit, mem_union_left _ (hs mis)⟩
    simp_rw [this, or_false] at ht
    have : ¬t ⊆ c := not_subset.mpr ⟨i, mit, dj.notMem_of_mem_left_finset (hs mis)⟩
    exact ht.resolve_right this
  · refine .inr (.inl (union_subset hs ?_))
    have : ¬Disjoint t (b ∪ c) := not_disjoint_iff.mpr ⟨i, mit, mem_union_right _ (hs mis)⟩
    simp_rw [this, or_false] at ht
    have : ¬t ⊆ b := not_subset.mpr ⟨i, mit, dj.notMem_of_mem_right_finset (hs mis)⟩
    exact ht.resolve_left this
  · refine .inr (.inr (disjoint_union_left.mpr ⟨hs, ?_⟩))
    rw [disjoint_union_right] at hs
    have : ¬t ⊆ b := not_subset.mpr ⟨i, mit, hs.1.notMem_of_mem_left_finset mis⟩
    simp_rw [this, false_or] at ht
    have : ¬t ⊆ c := not_subset.mpr ⟨i, mit, hs.2.notMem_of_mem_left_finset mis⟩
    exact ht.resolve_left this

lemma pair_aux (hi : ∑ k ∈ {i, j}ᶜ, (a k).natAbs < (a i).natAbs)
    {b c : Finset (Fin n)} (dj : Disjoint b c) (h : ∑ i ∈ b, a i = ∑ i ∈ c, a i)
    (hprod : a i * a j ≤ 0) (mi : i ∈ b) : j ∈ b := by
  rw [← insert_erase mi, sum_insert (notMem_erase _ _), ← eq_sub_iff_add_eq] at h
  by_cases mj : j ∈ c
  · rw [← insert_erase mj, sum_insert (notMem_erase _ _), add_sub_assoc, ← sub_eq_iff_eq_add'] at h
    replace h := congrArg Int.natAbs h
    contrapose! h
    apply ne_of_gt
    calc
      _ ≤ _ := Int.natAbs_sub_le ..
      _ ≤ ∑ k ∈ c.erase j, (a k).natAbs + ∑ k ∈ b.erase i, (a k).natAbs := by
        zify
        gcongr <;> exact abs_sum_le_sum_abs ..
      _ ≤ _ := by
        rw [← sum_union (dj.symm.mono (erase_subset _ _) (erase_subset _ _))]
        apply sum_le_sum_of_subset
        rw [subset_compl_comm]
        simp [dj.notMem_of_mem_left_finset mi, h]
      _ < _ := hi
      _ ≤ _ := by
        rw [Int.mul_nonpos_iff] at hprod
        lia
  · replace h := congrArg Int.natAbs h
    contrapose! h
    apply ne_of_gt
    calc
      _ ≤ _ := Int.natAbs_sub_le ..
      _ ≤ ∑ i ∈ c, (a i).natAbs + ∑ i ∈ b.erase i, (a i).natAbs := by
        zify
        gcongr <;> exact abs_sum_le_sum_abs ..
      _ ≤ _ := by
        rw [← sum_union (dj.symm.mono_right (erase_subset _ _))]
        apply sum_le_sum_of_subset
        rw [subset_compl_comm]
        simp [dj.notMem_of_mem_left_finset mi, h, mj]
      _ < _ := hi

/-- If there are two elements of opposite signs, each dominating the remaining `n - 2` elements
(in the sense of violating the triangle inequality), the two elements form a subsum block. -/
theorem pair_of_sum_natAbs_lt (hi : ∑ k ∈ {i, j}ᶜ, (a k).natAbs < (a i).natAbs)
    (hj : ∑ k ∈ {i, j}ᶜ, (a k).natAbs < (a j).natAbs) (hprod : a i * a j ≤ 0) :
    IsSubsumBlock a {i, j} := fun b c dj hs ↦ by
  have bpair : i ∈ b ↔ j ∈ b :=
    ⟨pair_aux hi dj hs hprod,
      pair_aux (by simpa [pair_comm] using hj) dj hs (by simpa [mul_comm] using hprod)⟩
  have cpair : i ∈ c ↔ j ∈ c :=
    ⟨pair_aux hi dj.symm hs.symm hprod,
      pair_aux (by simpa [pair_comm] using hj) dj.symm hs.symm (by simpa [mul_comm] using hprod)⟩
  by_cases mib : i ∈ b
  · apply Or.inl
    rwa [insert_subset_iff, singleton_subset_iff, ← bpair, and_self]
  by_cases mic : i ∈ c
  · refine .inr (.inl ?_)
    rwa [insert_subset_iff, singleton_subset_iff, ← cpair, and_self]
  refine .inr (.inr ?_)
  simp_all

variable (a s) in
/-- `reduce a s` is the tuple with `∑ i ∈ s, a i` at index 0
and the remaining elements of `a` appended unchanged. -/
def reduce : Fin (n - #s + 1) → ℤ :=
  Fin.cases (∑ i ∈ s, a i) (fun i ↦ a (sᶜ.orderIsoOfFin (by simp [card_compl]) i))

/-- Reduce a subsum block to a single element when proving the strong subsum condition. -/
theorem strongSSC_reduce (p : IsSubsumBlock a s) (ns : s.Nonempty) (h : StrongSSC (reduce a s)) :
    StrongSSC a := by
  sorry

end IsSubsumBlock
