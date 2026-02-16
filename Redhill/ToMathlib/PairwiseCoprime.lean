import Mathlib.RingTheory.Coprime.Lemmas

lemma Int.isCoprime_iff_natAbs_coprime {a b : ℤ} : IsCoprime a b ↔ a.natAbs.Coprime b.natAbs := by
  wlog ha : 0 ≤ a generalizing a
  · replace ha : 0 ≤ -a := by lia
    specialize this ha
    rwa [IsCoprime.neg_left_iff, natAbs_neg] at this
  wlog hb : 0 ≤ b generalizing b
  · replace hb : 0 ≤ -b := by lia
    specialize this hb
    rwa [IsCoprime.neg_right_iff, natAbs_neg] at this
  lift a to ℕ using ha
  lift b to ℕ using hb
  simp

lemma Int.pairwise_isCoprime_iff {a : Multiset ℤ} :
    a.Pairwise IsCoprime ↔ (a.map Int.natAbs).Pairwise Nat.Coprime := by
  rw [← Multiset.coe_toList a, Multiset.pairwise_coe_iff_pairwise fun _ _ a ↦ a.symm,
    Multiset.map_coe, Multiset.pairwise_coe_iff_pairwise fun _ _ a ↦ Nat.coprime_comm.mp a]
  simp_rw [List.pairwise_map, ← Int.isCoprime_iff_natAbs_coprime]
