module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Radical.Basic
public import Redhill.ToMathlib.MaxAbs

@[expose] public section

open Finset Real ENNReal

variable {n : ℕ}

open UniqueFactorizationMonoid in
/-- The quality of a single tuple.
This depends on Lean defining `log -x = log x` for all real `x`. -/
noncomputable def tupleQuality (a : Fin n → ℤ) : ℝ≥0∞ :=
  .ofReal (log (maxAbs a) / log (radical (∏ i, a i) : ℤ))

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

lemma quality_union_finite (h : B.Finite) : quality (A ∪ B) = quality A := by
  refine le_antisymm (sInf_le_sInf fun q mq ↦ ?_) (quality_mono Set.subset_union_left)
  simp only [Set.mem_setOf, Set.mem_union, Set.sep_union, Set.finite_union] at mq ⊢
  refine ⟨mq, h.subset (Set.sep_subset ..)⟩

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
