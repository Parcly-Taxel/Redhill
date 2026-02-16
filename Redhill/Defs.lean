import Redhill.Quality

section SSC

/-- The subsum condition: any subset of the multiset summing to 0
is either empty or the whole multiset. -/
def SSC (a : Multiset ℤ) : Prop :=
  ∀ b < a, b.sum = 0 → b = 0

/-- The stronger subsum condition, which is the subsum condition with negative weights allowed. -/
def StrongSSC (a : Multiset ℤ) : Prop :=
  ∀ p n, p + n < a → 0 < p + n → p.sum ≠ n.sum

variable {a : Multiset ℤ}

lemma SSC_of_strongSSC (h : StrongSSC a) : SSC a := by
  unfold SSC StrongSSC at *
  contrapose! h
  obtain ⟨b, lb, sb, nzb⟩ := h
  exact ⟨b, 0, by rwa [add_zero], by simp [nzb, pos_iff_ne_zero], by simp [sb]⟩

open Multiset in
lemma zero_notMem_of_SSC (hc : 2 ≤ a.card) (hs : a.sum = 0) (ha : SSC a) :
    0 ∉ a := by
  unfold SSC at ha
  contrapose! ha
  refine ⟨_, erase_lt.mpr ha, ?_, ?_⟩
  · rwa [← zero_add (a.erase 0).sum, sum_erase ha]
  · have cd : 0 < (a.erase 0).card := by grind [card_erase_add_one ha]
    rwa [card_pos] at cd

lemma zero_notMem_of_strongSSC (hc : 2 ≤ a.card) (hs : a.sum = 0) (ha : StrongSSC a) : 0 ∉ a :=
  zero_notMem_of_SSC hc hs (SSC_of_strongSSC ha)

end SSC

/- ### The conjectures -/

/-- The **abc conjecture** itself, using `quality`. -/
def ABCConjecture : Prop :=
  quality {a | a.card = 3 ∧ a.sum = 0 ∧ 0 ∉ a ∧ a.gcd = 1} = 1

/-- The multisets in Browkin and Brzeziński's `n`-conjecture. `A(n)` in the paper. -/
def nConjectureMultisets (n : ℕ) : Set (Multiset ℤ) :=
  {a | a.card = n ∧ a.sum = 0 ∧ SSC a ∧ a.gcd = 1}

/-- Browkin and Brzeziński's **`n`-conjecture** for a fixed `n`.
The conjecture itself is `∀ n ≥ 3, NConjecture n`. -/
def NConjecture (n : ℕ) : Prop :=
  quality (nConjectureMultisets n) = (2 * n - 5 : ℕ)

/-- The multisets in Browkin's strong `n`-conjecture. `B(n)` in the paper. -/
def strongNConjectureMultisets (n : ℕ) : Set (Multiset ℤ) :=
  {a | a.card = n ∧ a.sum = 0 ∧ a.Pairwise IsCoprime ∧ 0 ∉ a}

/-- Browkin's **strong `n`-conjecture** for a fixed `n`.
The conjecture itself is `∀ n ≥ 3, StrongNConjecture n`. -/
def StrongNConjecture (n : ℕ) : Prop :=
  quality (strongNConjectureMultisets n) < ⊤

/-- The multisets in Ramaekers's conjecture. `R(n)` in the paper. -/
def ramaekersMultisets (n : ℕ) : Set (Multiset ℤ) :=
  {a | a.card = n ∧ a.sum = 0 ∧ SSC a ∧ a.Pairwise IsCoprime}

/-- **Ramaekers's conjecture** for a fixed `n`.
The conjecture itself is `∀ n ≥ 3, RamaekersConjecture n`. -/
def RamaekersConjecture (n : ℕ) : Prop :=
  quality (ramaekersMultisets n) = 1

/-- `U(F,n)` in the paper. -/
def factorFreeMultisets (F : Finset ℕ) (n : ℕ) : Set (Multiset ℤ) :=
  {a | a.card = n ∧ a.sum = 0 ∧ StrongSSC a ∧ a.Pairwise IsCoprime ∧ ∀ f ∈ F, ∀ z ∈ a, ¬↑f ∣ z}
