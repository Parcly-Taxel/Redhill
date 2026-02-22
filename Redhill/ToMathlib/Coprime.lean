import Mathlib.RingTheory.Coprime.Lemmas

namespace IsCoprime

variable {R : Type*} [CommRing R] {x y : R}

lemma add_one_left_of_dvd (h : y ∣ x) : IsCoprime (x + 1) y := by
  obtain ⟨z, rfl⟩ := h
  rw [mul_add_left_left_iff]
  exact isCoprime_one_left

lemma add_one_right_of_dvd (h : x ∣ y) : IsCoprime x (y + 1) :=
  isCoprime_comm.mp (add_one_left_of_dvd h)

lemma sub_one_left_of_dvd (h : y ∣ x) : IsCoprime (x - 1) y := by
  rw [← neg_sub, neg_left_iff, sub_eq_neg_add]
  exact add_one_left_of_dvd h.neg_right

lemma sub_one_right_of_dvd (h : x ∣ y) : IsCoprime x (y - 1) :=
  isCoprime_comm.mp (sub_one_left_of_dvd h)

lemma add_one_sub_one_of_even (h : 2 ∣ x) : IsCoprime (x + 1) (x - 1) := by
  have key := add_mul_left_left (sub_one_right_of_dvd h) 1
  rwa [show 2 + (x - 1) * 1 = x + 1 by ring] at key

end IsCoprime

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
