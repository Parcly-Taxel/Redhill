module

public import Redhill.Common.PairwiseCoprime
public import Redhill.General.Defs

@[expose] public section

namespace GeneralCase

open Fin Filter IsCoprime

variable {n : ℕ} {F : Finset ℕ} {h : ℕ}

lemma isCoprime_natAdd_four_five :
    IsCoprime (tup n F h (natAdd n 4)) (tup n F h (natAdd n 5)) := by
  rw [tup_natAdd_four, tup_natAdd_five]
  apply (pow_left ?_).pow_right.neg_right
  rw [← add_mul_right_left_iff (z := -1)]
  ring_nf
  apply (mul_left ?_ ?_).neg_left
  · rw [← add_mul_left_right_iff (z := -1), mul_neg_one, add_neg_cancel_right,
      Nat.isCoprime_iff_coprime]
    exact X_coprime_Y.symm
  · rw [← Nat.cast_add, ← Nat.cast_two, Nat.isCoprime_iff_coprime, Nat.coprime_two_left]
    exact odd_X.add_even (even_iff_two_dvd.mpr dvd_Y.1.1)

lemma isCoprime_natAdd_three_four :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (natAdd n 3)) (tup n F h (natAdd n 4)) := by
  refine eventually_X_modEq_10Ym1 (F := F).mono fun h hx ↦ ?_
  simp_rw [tup_natAdd_three, tup_natAdd_four]
  apply (mul_left ?_ (pow_left ?_)).pow_right
  · rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, Nat.cast_one, dvd_sub_comm] at hx
    obtain ⟨m, hm⟩ := hx
    rw [sub_eq_iff_eq_add] at hm
    rw [show (10 * Y F - 1 : ℤ) = (10 * Y F - 1 : ℕ) by grind [Y_pos], hm, add_sub_assoc,
      mul_add_left_right_iff, show (1 - Y F : ℤ) = -(Y F - 1 : ℕ) by grind [Y_pos], neg_right_iff,
      Nat.isCoprime_iff_coprime]
    exact Ym1_coprime_10Ym1.symm
  · rw [← add_mul_left_right_iff (z := -1), mul_neg_one, ← sub_eq_add_neg, sub_sub_cancel_left,
      neg_right_iff, Nat.isCoprime_iff_coprime]
    exact X_coprime_Y

lemma isCoprime_natAdd_three_five :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (natAdd n 3)) (tup n F h (natAdd n 5)) := by
  refine eventually_X_modEq_10Ym1 (F := F).mono fun h hx ↦ ?_
  rw [tup_natAdd_three, tup_natAdd_five]
  apply (mul_left ?_ (pow_left ?_)).pow_right.neg_right
  · rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, Nat.cast_one, dvd_sub_comm] at hx
    obtain ⟨m, hm⟩ := hx
    rw [sub_eq_iff_eq_add] at hm
    rw [show (10 * Y F - 1 : ℤ) = (10 * Y F - 1 : ℕ) by grind [Y_pos], hm, add_assoc,
      mul_add_left_right_iff, add_comm, ← Nat.cast_add_one, Nat.isCoprime_iff_coprime]
    exact Yp1_coprime_10Ym1.symm
  · rw [← add_mul_left_right_iff (z := -1), mul_neg_one, ← sub_eq_add_neg, add_sub_cancel_left,
      Nat.isCoprime_iff_coprime]
    exact X_coprime_Y

lemma isCoprime_natAdd_two_three :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (natAdd n 2)) (tup n F h (natAdd n 3)) := by
  refine eventually_X_modEq_10Ym1 (F := F).mono fun h hx ↦ ?_
  rw [tup_natAdd_two, tup_natAdd_three]
  apply (mul_right ?_ (pow_right ?_)).pow_left
  · sorry
  · sorry

theorem pairwiseCoprime_tup : ∀ᶠ h in atTop, PairwiseCoprime (tup n F h) := by
  sorry

end GeneralCase
