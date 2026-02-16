import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Redhill.Radical

/-- The maximum absolute value of a multiset of integers (0 for the empty multiset). -/
def maxAbs (a : Multiset ℤ) : ℕ :=
  (a.map Int.natAbs).fold max 0

variable {a : Multiset ℤ}

lemma prod_natAbs_comm : a.prod.natAbs = (a.map Int.natAbs).prod := by
  induction a using Multiset.induction with
  | empty => simp
  | cons n a ih => simp_rw [Multiset.map_cons, Multiset.prod_cons, ← ih, Int.natAbs_mul]

lemma le_maxAbs {l : ℕ} (ha : ∃ n ∈ a, l ≤ n.natAbs) : l ≤ maxAbs a := by
  obtain ⟨n, mn, hn⟩ := ha
  rw [← Multiset.cons_erase mn, maxAbs, Multiset.map_cons, Multiset.fold_cons_left, le_max_iff]
  exact .inl hn

open Real ENNReal

/-- The quality of a single multiset. -/
noncomputable def multisetQuality (a : Multiset ℤ) : ℝ≥0∞ :=
  .ofReal (log (maxAbs a) / log a.prod.natAbs.radical)

/-- The quality of a set of multisets. -/
noncomputable def quality (A : Set (Multiset ℤ)) : ℝ≥0∞ :=
  sInf {q | {a ∈ A | q < multisetQuality a}.Finite}

variable {A B : Set (Multiset ℤ)} {q : ℝ≥0∞}

lemma quality_mono (h : A ⊆ B) : quality A ≤ quality B :=
  sInf_le_sInf fun _ mq ↦ mq.subset fun _ ma ↦ ⟨h ma.1, ma.2⟩

lemma quality_le_of_finite (hq : {a ∈ A | q < multisetQuality a}.Finite) : quality A ≤ q :=
  CompleteSemilatticeInf.sInf_le _ q hq

lemma quality_finite (hA : A.Finite) : quality A = 0 := by
  rw [← nonpos_iff_eq_zero]
  exact quality_le_of_finite (hA.sep _)

lemma quality_empty : quality ∅ = 0 :=
  quality_finite Set.finite_empty

open Filter Topology in
lemma quality_ge_of_liminf (f : ℕ ↪ Multiset ℤ) (rf : Set.range f ⊆ A)
    (qf : q ≤ liminf (multisetQuality ∘ f) atTop) : q ≤ quality A := by
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
