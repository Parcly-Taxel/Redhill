module

public import Redhill.Defs

@[expose] public section

namespace BB94

open Nat Finset

/-- The coefficient of `x^j` in the paper's `f_k(x)`. This is [OEIS A111125](https://oeis.org/A111125). -/
def C (k j : ℕ) : ℕ :=
  (k + j).choose (2 * j) + 2 * (k + j).choose (2 * j + 1)
  -- (k + j).choose (2 * j) * (2 * k + 1) / (2 * j + 1)

variable {k j : ℕ}

lemma C_eq_zero_iff : C k j = 0 ↔ k < j := by
  simp_rw [C, Nat.add_eq_zero_iff, mul_eq_zero, two_ne_zero, false_or, choose_eq_zero_iff]
  lia

alias ⟨_, C_eq_zero_of_lt⟩ := C_eq_zero_iff

@[simp]
lemma C_zero : C k 0 = 2 * k + 1 := by
  simp [C, add_comm]

@[simp]
lemma C_self : C k k = 1 := by
  simp [C, two_mul]

lemma C_add_two_add_one :
    C (k + 2) (j + 1) = 2 * C (k + 1) (j + 1) + C (k + 1) j - C k (j + 1) := by
  grind [C]

lemma C_mono_right : Monotone (C · j) := fun k₁ k₂ h ↦ by
  simp only [C]
  gcongr

lemma C_le : C k (j + 1) ≤ 2 * C (k + 1) (j + 1) + C (k + 1) j :=
  calc
    _ ≤ C (k + 1) (j + 1) := C_mono_right (Nat.le_add_right ..)
    _ ≤ _ := by lia

theorem sum_Icc_C_mul (x y : ℤ) :
    x ^ (2 * k + 1) + y ^ (2 * k + 1) =
    ∑ j ∈ range (k + 1), C k j * (x + y) ^ (2 * j + 1) * (-x * y) ^ (k - j) := by
  induction k using twoStepInduction with
  | zero => simp
  | one => simp [show range 2 = {0, 1} by decide]; ring
  | more k ih₀ ih₁ =>
    set s := x + y
    set p := -x * y
    have decomp :
        x^(2*(k+2)+1) + y^(2*(k+2)+1) =
        2 * (p * (x^(2*(k+1)+1) + y^(2*(k+1)+1)) - C (k+1) 0 * s * p^(k+2)) +
        s^2 * (x^(2*(k+1)+1) + y^(2*(k+1)+1)) -
        (p^2 * (x^(2*k+1) + y^(2*k+1)) - C k 0 * s * p^(k+2)) +
        C (k+2) 0 * s * p ^ (k+2) := by
      simp [C_zero]
      ring
    conv_rhs =>
      rw [sum_range_succ']
      enter [1, 2, j]
      rw [C_add_two_add_one, cast_sub C_le, cast_add, cast_mul, cast_two, mul_assoc, sub_mul,
        add_mul, mul_assoc]
    rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, decomp]
    clear decomp
    congr
    · symm
      rw [sum_range_succ, C_eq_zero_of_lt (by lia), cast_zero, zero_mul, add_zero]
      let g (j : ℕ) := C (k + 1) j * (s ^ (2 * j + 1) * p ^ (k + 2 - j))
      change ∑ j ∈ range (k + 1), g (j + 1) = _
      have g0 : g 0 = C (k + 1) 0 * s * p ^ (k + 2) := by simp [g, mul_assoc]
      rw [range_eq_Ico, sum_Ico_add', zero_add, ← g0, eq_sub_iff_add_eq',
        ← sum_range_eq_add_Ico _ (by lia), ih₁, mul_sum]
      congr! 1 with j hj
      rw [mem_range] at hj
      simp_rw [g, show k + 2 - j = k + 1 - j + 1 by lia]
      ring
    · rw [ih₁, mul_sum]
      congr! 1 with j hj
      rw [show k + 2 - (j + 1) = k + 1 - j by lia]
      ring
    · symm
      iterate 2 rw [sum_range_succ, C_eq_zero_of_lt (by lia), cast_zero, zero_mul, add_zero]
      let g (j : ℕ) := C k j * (s ^ (2 * j + 1) * p ^ (k + 2 - j))
      change ∑ j ∈ range k, g (j + 1) = _
      have g0 : g 0 = C k 0 * s * p ^ (k + 2) := by simp [g, mul_assoc]
      rw [range_eq_Ico, sum_Ico_add', zero_add, ← g0, eq_sub_iff_add_eq',
        ← sum_range_eq_add_Ico _ (by lia), ih₀, mul_sum]
      congr! 1 with j hj
      rw [mem_range] at hj
      simp_rw [g, show k + 2 - j = k - j + 2 by lia]
      ring
    · simp

end BB94

#eval (List.range 10).map fun k ↦ (List.range (k + 1)).map (BB94.C k)

/-- Theorem 1.3 in the paper, Browkin and Brzeziński (1994). -/
lemma le_quality_nConjectureTuples {n : ℕ} (hn : 3 ≤ n) :
    (2 * n - 5 : ℕ) ≤ quality (nConjectureTuples n) := by
  sorry
