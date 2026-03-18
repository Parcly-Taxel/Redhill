module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic.Zify

@[expose] public section

open Finset

variable {n k : ℕ} (a : Fin n → ℤ)

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

lemma strongSSC_perm (e : Equiv.Perm (Fin n)) (h : StrongSSC a) : StrongSSC (a ∘ e) := by
  intro b c dj n₁ n₂
  specialize h (b.map e) (c.map e)
  simp_rw [disjoint_map, union_nonempty, map_nonempty, ← union_nonempty, sum_map] at h
  apply h dj n₁
  obtain ⟨i, mi⟩ := n₂
  exact ⟨e i, by simp_all⟩

lemma strongSSC_perm_iff (e : Equiv.Perm (Fin n)) : StrongSSC a ↔ StrongSSC (a ∘ e) where
  mp h := strongSSC_perm e h
  mpr h := by simpa [Function.comp_assoc] using strongSSC_perm e.symm h

section TupReduce

variable (s : Finset (Fin n)) (hk : k = n - #s)

/-- The order-preserving bijection from `Fin k` to `sᶜ`, where `k = n - #s`. -/
def complRank (i : Fin k) : Fin n :=
  sᶜ.orderEmbOfFin (by simp [card_compl]) (i.cast hk)

lemma complRank_01 : complRank {0, 1} (n.add_sub_cancel 2).symm = (Fin.addNat · 2) :=
  (orderEmbOfFin_unique _ (by simp [Fin.ext_iff]) (Fin.strictMono_addNat 2)).symm

variable (a) in
/-- `tupReduce a s hk` is the tuple with `∑ i ∈ s, a i` at index 0
and the remaining elements of `a` appended in order.
`hk : k = n - #s` mitigates definitional equality problems. -/
def tupReduce : Fin (k + 1) → ℤ :=
  Fin.cases (∑ i ∈ s, a i) fun i ↦ a (complRank s hk i)

lemma tupReduce_01_zero {a : Fin (n + 2) → ℤ} :
    tupReduce a {0, 1} (n.add_sub_cancel 2).symm 0 = a 0 + a 1 := by
  simp [tupReduce, complRank_01]

lemma tupReduce_01_succ {a : Fin (n + 2) → ℤ} {i : Fin n} :
    tupReduce a {0, 1} (n.add_sub_cancel 2).symm i.succ = a (i.addNat 2) := by
  simp [tupReduce, complRank_01]

variable {s hk}

lemma injective_complRank : (complRank s hk).Injective := fun i j h ↦ by
  simpa [complRank] using h

lemma range_complRank : Set.range (complRank s hk) = sᶜ := by
  unfold complRank
  subst hk
  simp_all

lemma eq_map_complRank {b : Finset (Fin n)} (hb : Disjoint s b) :
    b = map ⟨complRank s hk, injective_complRank⟩ {i | complRank s hk i ∈ b} := by
  ext i
  simp_rw [mem_map, mem_filter_univ, Function.Embedding.coeFn_mk]
  refine ⟨fun h ↦ ?_, fun ⟨a, ma, ha⟩ ↦ ha.symm ▸ ma⟩
  have : i ∈ Set.range (complRank s hk) := by
    rw [range_complRank, mem_coe, mem_compl]
    exact hb.notMem_of_mem_right_finset h
  obtain ⟨a, ha⟩ := this
  refine ⟨a, by simp_all⟩

end TupReduce

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

/-- Reduce a subsum block to a single element when proving the strong subsum condition. -/
theorem strongSSC_tupReduce (p : IsSubsumBlock a s) (hk : k = n - #s)
    (h : StrongSSC (tupReduce a s hk)) : StrongSSC a := by
  unfold StrongSSC at *
  contrapose! h
  obtain ⟨b, c, dj, n₁, n₂, hs⟩ := h
  specialize p b c dj hs
  rw [← or_rotate, disjoint_union_right] at p
  obtain p | p := p
  · let b' : Finset (Fin k) := {i | complRank s hk i ∈ b}
    let c' : Finset (Fin k) := {i | complRank s hk i ∈ c}
    have eqb : b = b'.map _ := eq_map_complRank p.1
    have eqc : c = c'.map _ := eq_map_complRank p.2
    refine ⟨b'.map (Fin.succEmb k), c'.map (Fin.succEmb k), by simp_all, by simp_all, ?_, ?_⟩
    · exact ⟨0, by simp [b', c']⟩
    · simp_all [tupReduce]
  wlog q : s ⊆ b generalizing b c
  · rw [union_comm] at n₁ n₂
    exact this c b dj.symm n₁ n₂ hs.symm p.symm (p.resolve_left q)
  replace p := dj.mono_left q
  let b' : Finset (Fin k) := {i | complRank s hk i ∈ b \ s}
  let c' : Finset (Fin k) := {i | complRank s hk i ∈ c}
  have eqb : b \ s = b'.map _ := eq_map_complRank disjoint_sdiff
  have eqc : c = c'.map _ := eq_map_complRank p
  refine ⟨insert 0 (b'.map (Fin.succEmb k)), c'.map (Fin.succEmb k), ?_, by simp, ?_, ?_⟩
  · have : Disjoint (b \ s) c := dj.mono_left sdiff_le
    simp_all
  · obtain ⟨i, mi⟩ := n₂
    have ni : i ∉ s := by
      contrapose! mi
      rw [notMem_compl, mem_union]
      exact .inl (q mi)
    rw [← mem_compl, ← mem_coe, ← range_complRank (hk := hk), Set.mem_range] at ni
    obtain ⟨j, rfl⟩ := ni
    refine ⟨j.succ, ?_⟩
    simp [b', c']
    simp_all
  · rw [← sum_sdiff q, add_comm] at hs
    simp_all [tupReduce]

end IsSubsumBlock
