import Redhill.Quality
import Redhill.SubsumCondition

open Finset

/-- A predicate stating that the given tuple's numbers are pairwise coprime. -/
def PairwiseCoprime {n : ℕ} (a : Fin n → ℤ) : Prop :=
  ∀ i j, i ≠ j → IsCoprime (a i) (a j)

/-- The **abc conjecture** itself, using `quality`. -/
def ABCConjecture : Prop :=
  quality {a : Fin 3 → ℤ | ∑ i, a i = 0 ∧ univ.gcd a = 1} = 1

/-- The tuples in Browkin and Brzeziński's `n`-conjecture. `A(n)` in the paper. -/
def nConjectureTuples (n : ℕ) : Set (Fin n → ℤ) :=
  {a | ∑ i, a i = 0 ∧ SSC a ∧ univ.gcd a = 1}

/-- Browkin and Brzeziński's **`n`-conjecture** for a fixed `n`.
The conjecture itself is `∀ n ≥ 3, NConjecture n`. -/
def NConjecture (n : ℕ) [NeZero n] : Prop :=
  quality (nConjectureTuples n) = (2 * n - 5 : ℕ)

/-- The tuples in Browkin's strong `n`-conjecture. `B(n)` in the paper. -/
def strongNConjectureTuples (n : ℕ) : Set (Fin n → ℤ) :=
  {a | ∑ i, a i = 0 ∧ PairwiseCoprime a}

/-- Browkin's **strong `n`-conjecture** for a fixed `n`.
The conjecture itself is `∀ n ≥ 3, StrongNConjecture n`. -/
def StrongNConjecture (n : ℕ) [NeZero n] : Prop :=
  quality (strongNConjectureTuples n) < ⊤

/-- The tuples in Ramaekers's conjecture. `R(n)` in the paper. -/
def ramaekersTuples (n : ℕ) : Set (Fin n → ℤ) :=
  {a | ∑ i, a i = 0 ∧ SSC a ∧ PairwiseCoprime a}

/-- **Ramaekers's conjecture** for a fixed `n`.
The conjecture itself is `∀ n ≥ 3, RamaekersConjecture n`. -/
def RamaekersConjecture (n : ℕ) [NeZero n] : Prop :=
  quality (ramaekersTuples n) = 1

/-- `U(F,n)` in the paper. -/
def factorFreeTuples (F : Finset ℕ) (n : ℕ) : Set (Fin n → ℤ) :=
  {a | ∑ i, a i = 0 ∧ StrongSSC a ∧ PairwiseCoprime a ∧ ∀ f ∈ F, ∀ i, ¬↑f ∣ a i}

lemma nConjecture_3_iff_ABC : NConjecture 3 ↔ ABCConjecture := by
  unfold NConjecture ABCConjecture nConjectureTuples
  norm_num
  sorry

/-- Theorem 1.3 in the paper, Browkin and Brzeziński (1994). -/
lemma le_quality_nConjectureTuples {n : ℕ} (hn : 3 ≤ n) :
    have : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
    (2 * n - 5 : ℕ) ≤ quality (nConjectureTuples n) := by
  sorry
