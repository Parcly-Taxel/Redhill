module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Sign.Defs

@[expose] public section

open Finset SignType

variable {n k : ℕ} (a : Fin n → ℤ)

/-- The subsum condition: any subset of the tuple summing to 0
is either empty or the whole tuple. -/
def SSC : Prop :=
  ∀ b, b.Nonempty → bᶜ.Nonempty → ∑ i ∈ b, a i ≠ 0

/-- A subsum block for `a` is an index set that must be constant in any sign weighting
of the tuple's elements that leads to a zero sum. -/
def IsSubsumBlock (s : Finset (Fin n)) : Prop :=
  ∀ b : Fin n → SignType, ∑ i, b i * a i = 0 → ∃ c, ∀ i ∈ s, b i = c

/-- The strong subsum condition, defined as all `Fin n` being a subsum block. -/
def StrongSSC : Prop :=
  IsSubsumBlock a univ

variable {a}

lemma SSC_of_strongSSC (h : StrongSSC a) : SSC a := by
  unfold SSC StrongSSC IsSubsumBlock at *
  contrapose! h
  obtain ⟨b, n₁, n₂, hs⟩ := h
  refine ⟨fun i ↦ if i ∈ b then pos else zero, ?_, fun c ↦ ?_⟩
  · simp_rw [pos_eq_one, zero_eq_zero, apply_ite, coe_one, coe_zero, ite_mul, one_mul, zero_mul,
      ← sum_filter, filter_univ_mem, hs]
  · obtain ⟨i₁, mi₁⟩ := n₁
    obtain ⟨i₂, mi₂⟩ := n₂
    match c with
    | zero => exact ⟨i₁, mem_univ _, by simp_all⟩
    | neg => exact ⟨i₁, mem_univ _, by simp_all⟩
    | pos => exact ⟨i₂, mem_univ _, by simp_all⟩

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

lemma strongSSC_perm (e : Equiv.Perm (Fin n)) (h : StrongSSC a) : StrongSSC (a ∘ e) := fun b hs ↦ by
  have : b = (b ∘ e.symm) ∘ e := by simp [Function.comp_assoc]
  conv_lhs at hs =>
    enter [2, i]
    rw [this, Function.comp_apply]
    enter [2]
    rw [Function.comp_apply]
  rw [e.sum_comp univ (fun i ↦ (b ∘ e.symm) i * a i) (by simp)] at hs
  specialize h _ hs
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun i _ ↦ ?_⟩
  specialize hc (e i) (mem_univ _)
  simpa using hc

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

lemma image_complRank_univ : univ.image (complRank s hk) = sᶜ := by
  unfold complRank
  subst hk
  simp_all

end TupReduce

namespace IsSubsumBlock

variable {i j : Fin n} {s t : Finset (Fin n)}

lemma empty : IsSubsumBlock a ∅ := fun b h ↦ by simp

lemma singleton : IsSubsumBlock a {i} := fun b h ↦ by simp

lemma subset (hs : IsSubsumBlock a s) (ht : t ⊆ s) : IsSubsumBlock a t := fun b h ↦
  (hs b h).imp fun _ hc _ mi ↦ hc _ (ht mi)

lemma union (hs : IsSubsumBlock a s) (ht : IsSubsumBlock a t) (hd : ¬Disjoint s t) :
    IsSubsumBlock a (s ∪ t) := fun b h ↦ by
  obtain ⟨c, hc⟩ := hs b h
  obtain ⟨c', hc'⟩ := ht b h
  have e : c = c' := by
    obtain ⟨i, hi₁, hi₂⟩ := not_disjoint_iff.mp hd
    grind
  exact ⟨c, fun i mi ↦ by grind⟩

theorem of_sum_natAbs_lt (f : Fin k ↪ Fin n)
    (hf : ∀ b : Fin k → SignType, (¬∃ c, ∀ i, b i = c) →
      ∑ i ∉ univ.map f, (a i).natAbs < (∑ i, b i * a (f i)).natAbs) :
    IsSubsumBlock a (univ.map f) := fun b hs ↦ by
  contrapose! hs
  simp only [mem_map, mem_univ, true_and, ↓existsAndEq] at hs
  specialize hf (b ∘ f)
  simp only [Function.comp_apply, not_exists, not_forall] at hf
  specialize hf hs
  rw [← sum_add_sum_compl (univ.map f), Ne, add_eq_zero_iff_eq_neg', sum_map]
  suffices (∑ i ∉ univ.map f, b i * a i).natAbs ≠ (∑ i, b (f i) * a (f i)).natAbs by
    contrapose this
    rw [this, Int.natAbs_neg]
  refine Int.natAbs_sum_le .. |>.trans (sum_le_sum fun i _ ↦ ?_) |>.trans_lt hf |>.ne
  cases b i <;> simp

/-- If there are two elements of opposite signs, each dominating the remaining `n - 2` elements
(in the sense of violating the triangle inequality), the two elements form a subsum block. -/
theorem pair_of_sum_natAbs_lt (hi : ∑ k ∈ {i, j}ᶜ, (a k).natAbs < (a i).natAbs)
    (hj : ∑ k ∈ {i, j}ᶜ, (a k).natAbs < (a j).natAbs) (hprod : a i * a j ≤ 0) :
    IsSubsumBlock a {i, j} := by
  obtain rfl | hn := eq_or_ne i j
  · simp [singleton]
  let f : Fin 2 ↪ Fin n := ⟨fun | 0 => i | 1 => j, fun i₁ i₂ h ↦ by grind⟩
  have mf : univ.map f = {i, j} := by ext k; simp [f]; grind
  rw [← mf]
  refine of_sum_natAbs_lt _ fun b ncb ↦ ?_
  simp only [mf, Fin.sum_univ_two, f, Function.Embedding.coeFn_mk]
  replace ncb : b 0 ≠ b 1 := by
    contrapose ncb
    refine ⟨b 1, fun k ↦ ?_⟩
    obtain rfl | rfl : k = 0 ∨ k = 1 := by lia
    · exact ncb
    · rfl
  cases e₀ : b 0 <;> cases e₁ : b 1 <;> simp [e₀, e₁] at ncb
  case zero.neg => simpa using hj
  case zero.pos => simpa using hj
  case neg.zero => simpa using hi
  case pos.zero => simpa using hi
  all_goals
    rw [Int.mul_nonpos_iff] at hprod
    simp only [pos_eq_one, neg_eq_neg_one, coe_neg, coe_one]
    grind

/-- Reduce a subsum block to a single element when proving the strong subsum condition. -/
theorem strongSSC_tupReduce (p : IsSubsumBlock a s) (hk : k = n - #s)
    (h : StrongSSC (tupReduce a s hk)) : StrongSSC a := by
  unfold StrongSSC IsSubsumBlock at *
  contrapose! h
  obtain ⟨b, hs, hc⟩ := h
  obtain ⟨c₀, hc₀⟩ := p _ hs
  refine ⟨Fin.cases c₀ (b ∘ complRank s hk), ?_, fun c ↦ ?_⟩
  · simp_rw [Fin.sum_univ_succ, tupReduce, Fin.cases_zero, Fin.cases_succ, Function.comp_apply]
    have io : (SetLike.coe univ).InjOn (complRank s hk) := by simp [injective_complRank]
    rw [← sum_image (f := fun i ↦ (b i) * a i) io, image_complRank_univ, mul_sum]
    have s_eq : ∑ i ∈ s, c₀ * a i = ∑ i ∈ s, b i * a i := sum_congr rfl fun i mi ↦ by rw [hc₀ _ mi]
    rwa [s_eq, sum_add_sum_compl]
  · obtain rfl | hn := eq_or_ne c₀ c
    · obtain ⟨i, -, hi⟩ := hc c₀
      have key : i ∈ sᶜ := by
        contrapose! hi
        exact hc₀ _ (notMem_compl.mp hi)
      rw [← image_complRank_univ (hk := hk), mem_image_univ_iff_mem_range, Set.mem_range] at key
      obtain ⟨j, rfl⟩ := key
      exact ⟨j.succ, mem_univ _, by simp [hi]⟩
    · exact ⟨0, mem_univ _, by simpa⟩

end IsSubsumBlock
