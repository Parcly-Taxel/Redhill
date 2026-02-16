import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Redhill.ToMathlib.Radical

open Finset

variable {n : ℕ} [NeZero n]

/-- The maximum absolute value of a tuple of integers. -/
def maxAbs (a : Fin n → ℤ) : ℕ :=
  (univ.image fun i ↦ (a i).natAbs).max' (by simp)

open Real ENNReal

/-- The quality of a single tuple. -/
noncomputable def tupleQuality (a : Fin n → ℤ) : ℝ≥0∞ :=
  .ofReal (log (maxAbs a) / log (∏ i, a i).natAbs.radical)

/-- The quality of a set of tuples, defined as the infimum of those numbers where
only finitely many tuples in the set have a strictly higher quality. -/
noncomputable def quality (A : Set (Fin n → ℤ)) : ℝ≥0∞ :=
  sInf {q | {a ∈ A | q < tupleQuality a}.Finite}

variable {A B : Set (Fin n → ℤ)} {q : ℝ≥0∞}

lemma quality_mono (h : A ⊆ B) : quality A ≤ quality B :=
  sInf_le_sInf fun _ mq ↦ mq.subset fun _ ma ↦ ⟨h ma.1, ma.2⟩

lemma quality_le_of_finite (hq : {a ∈ A | q < tupleQuality a}.Finite) : quality A ≤ q :=
  CompleteSemilatticeInf.sInf_le _ q hq

lemma quality_finite (hA : A.Finite) : quality A = 0 := by
  rw [← nonpos_iff_eq_zero]
  exact quality_le_of_finite (hA.sep _)

lemma quality_empty : quality (n := n) ∅ = 0 :=
  quality_finite Set.finite_empty

open Filter in
lemma quality_ge_of_liminf (f : ℕ ↪ Fin n → ℤ) (rf : Set.range f ⊆ A)
    (qf : q ≤ liminf (tupleQuality ∘ f) atTop) : q ≤ quality A := by
  rw [quality, le_sInf_iff]
  intro k lk
  contrapose! lk
  rw [le_liminf_iff] at qf
  replace qf := qf _ lk
  rw [eventually_atTop] at qf
  obtain ⟨N₀, hN₀⟩ := qf
  refine (Set.Ici_infinite N₀).image f.injective.injOn |>.mono fun a ma ↦ ?_
  obtain ⟨i, li, hi⟩ := ma
  exact ⟨rf ⟨_, hi⟩, hi ▸ hN₀ _ li⟩
