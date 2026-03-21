module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
This file contains two integer-related definitions, `PairwiseCoprime` and `maxAbs`.
-/

@[expose] public section

open Finset

variable {n : ℕ}

/-- A predicate stating that the given tuple's numbers are pairwise coprime. -/
def PairwiseCoprime (a : Fin n → ℤ) : Prop :=
  ∀ {i j}, i < j → IsCoprime (a i) (a j)

lemma gcd_one_of_pairwiseCoprime
    (hn : 2 ≤ n) {a : Fin n → ℤ} (ha : PairwiseCoprime a) : univ.gcd a = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨_, (Nat.sub_add_cancel hn).symm⟩
  specialize ha Fin.zero_lt_one
  rw [Int.isCoprime_iff_gcd_eq_one] at ha
  rw [← union_compl {0, 1}, gcd_union, gcd_insert, Finset.gcd, Finset.fold_singleton, ← gcd_assoc,
    ← Int.coe_gcd (a 0), ha, Nat.cast_one, gcd_one_left, gcd_one_left]

/-- The maximum absolute value of a tuple of integers (0 if empty). -/
def maxAbs (a : Fin n → ℤ) : ℕ :=
  univ.sup fun i ↦ (a i).natAbs

lemma maxAbs_zero {a : Fin 0 → ℤ} : maxAbs a = 0 := by simp [maxAbs]

lemma maxAbs_one {a : Fin 1 → ℤ} : maxAbs a = (a 0).natAbs := by simp [maxAbs]

variable {a : Fin n → ℤ}

lemma maxAbs_eq_foldr : maxAbs a = (List.ofFn fun i ↦ (a i).natAbs).foldr max 0 := by
  rw [← Nat.bot_eq_zero, List.foldr_sup_eq_sup_toFinset, maxAbs,
    ← (fun i ↦ (a i).natAbs).id_comp, ← sup_image]
  congr; ext; simp

lemma maxAbs_eq_of_forall_le {i : Fin n} (hi : ∀ j, (a j).natAbs ≤ (a i).natAbs) :
    maxAbs a = (a i).natAbs :=
  le_antisymm (Finset.sup_le (by simp_all)) (le_sup (f := fun i ↦ (a i).natAbs) (mem_univ _))
