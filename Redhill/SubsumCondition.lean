import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

open Finset

variable {n : ℕ}

/-- The subsum condition: any subset of the tuple summing to 0
is either empty or the whole tuple. -/
def SSC (a : Fin n → ℤ) : Prop :=
  ∀ b, b.Nonempty → bᶜ.Nonempty → ∑ i ∈ b, a i ≠ 0

/-- The stronger subsum condition: two disjoint sub-tuples with the same sum
must have their union either empty or the whole tuple. -/
def StrongSSC (a : Fin n → ℤ) : Prop :=
  ∀ b c, Disjoint b c → (b ∪ c).Nonempty → (b ∪ c)ᶜ.Nonempty → ∑ i ∈ b, a i ≠ ∑ i ∈ c, a i

variable {a : Fin n → ℤ}

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
