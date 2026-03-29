module

public import Redhill.Common.PairwiseCoprime
public import Redhill.General.Defs
public import Redhill.ToMathlib.Coprime

@[expose] public section

namespace GeneralCase

open Fin Filter IsCoprime

variable {n : ℕ} {F : Finset ℕ}

lemma isCoprime_natAdd_four_five {h : ℕ} :
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
    exact odd_X.add_even even_Y

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
  · have mcast : (10 * Y F - 1 : ℤ) = (10 * Y F - 1 : ℕ) := by grind [Y_pos]
    replace hx := hx.pow 2
    rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, one_pow, Nat.cast_one, dvd_sub_comm] at hx
    obtain ⟨m, hm⟩ := hx
    rw [sub_eq_iff_eq_add, Nat.cast_pow] at hm
    rw [hm, add_assoc, ← mcast, mul_add_left_left_iff,
      show 1 + 10 * (Y F : ℤ) ^ 3 = Y F ^ 2 + 1 + (10 * Y F - 1) * Y F ^ 2 by ring,
      add_mul_left_left_iff, ← add_mul_right_left_iff (z := 10 * (Y F : ℤ) + 1),
      ← mul_self_sub_one, ← sq, add_add_sub_cancel, mul_pow, ← one_add_mul]
    apply mul_left ?_ (pow_left ?_)
    · rw [mcast, show (1 + 10 ^ 2 : ℤ) = (101 : ℕ) by rfl, Nat.isCoprime_iff_coprime,
        (show Nat.Prime 101 by decide).coprime_iff_not_dvd]
      grind [hundredone_dvd_Y]
    · rw [sub_eq_add_neg, mul_add_right_right_iff, neg_right_iff]
      exact isCoprime_one_right
  · rw [sq, mul_add_right_left_iff, X, Nat.cast_pow]
    apply (mul_left ?_ (pow_left ?_)).pow_right
    · rw [Nat.cast_add_one]
      exact add_one_right_of_dvd (mod_cast ten_dvd_Y)
    · rw [Nat.isCoprime_iff_coprime]
      simp

lemma isCoprime_natAdd_two_sq_sub_sq :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (natAdd n 2)) (X F h ^ 2 - Y F ^ 2) := by
  refine eventually_X_modEq_10Yp1 (F := F).mono fun h hx ↦ ?_
  rw [tup_natAdd_two]
  apply pow_left
  rw [← add_mul_left_left_iff (z := -1), mul_neg_one, neg_sub, ← add_sub_assoc, add_assoc,
    add_sub_cancel_left, pow_succ', ← mul_assoc, ← add_one_mul, sq_sub_sq]
  refine mul_left ?_ (pow_left (mul_right ?_ ?_))
  · rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, Nat.cast_one, dvd_sub_comm] at hx
    obtain ⟨m, hm⟩ := hx
    rw [sub_eq_iff_eq_add] at hm
    rw [show (10 * Y F + 1 : ℤ) = (10 * Y F + 1 : ℕ) by lia, hm]
    apply mul_right
    · rw [add_assoc, mul_add_left_right_iff, add_comm (1 : ℤ), ← Nat.cast_add_one,
        Nat.isCoprime_iff_coprime]
      exact Yp1_coprime_10Yp1.symm
    · rw [add_sub_assoc, mul_add_left_right_iff,
        show (1 - Y F : ℤ) = -(Y F - 1 : ℕ) by grind [Y_pos], neg_right_iff,
        Nat.isCoprime_iff_coprime]
      exact Ym1_coprime_10Yp1.symm
  · rw [← add_mul_left_right_iff (z := -1), mul_neg_one, add_neg_cancel_right,
      Nat.isCoprime_iff_coprime]
    exact X_coprime_Y.symm
  · rw [← add_mul_left_right_iff (z := 1), mul_one, sub_add_cancel, Nat.isCoprime_iff_coprime]
    exact X_coprime_Y.symm

lemma isCoprime_natAdd_two_four :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (natAdd n 2)) (tup n F h (natAdd n 4)) := by
  refine isCoprime_natAdd_two_sq_sub_sq (n := n) (F := F).mono fun h hx ↦ ?_
  rw [sq_sub_sq, mul_right_iff] at hx
  rw [tup_natAdd_four]
  exact hx.2.pow_right

lemma isCoprime_natAdd_two_five :
    ∀ᶠ h in atTop, IsCoprime (tup n F h (natAdd n 2)) (tup n F h (natAdd n 5)) := by
  refine isCoprime_natAdd_two_sq_sub_sq (n := n) (F := F).mono fun h hx ↦ ?_
  rw [sq_sub_sq, mul_right_iff] at hx
  rw [tup_natAdd_five]
  exact hx.1.pow_right.neg_right

theorem pairwiseCoprime_tup : ∀ᶠ h in atTop, PairwiseCoprime (tup n F h) := by
  sorry

end GeneralCase
