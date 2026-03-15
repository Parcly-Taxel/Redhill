module

public import Redhill.Defs

@[expose] public section

namespace BB94

open Nat Finset

/-- The coefficient of `x^j` in the paper's `f_k(x)`. This is [OEIS A111125](https://oeis.org/A111125). -/
def C (k j : ℕ) : ℕ :=
  (k + j).choose (2 * j) + 2 * (k + j).choose (2 * j + 1)
  -- (k + j).choose (2 * j) * (2 * k + 1) / (2 * j + 1)

section

variable {k j : ℕ}

lemma C_eq_zero_iff : C k j = 0 ↔ k < j := by
  simp_rw [C, Nat.add_eq_zero_iff, mul_eq_zero, two_ne_zero, false_or, choose_eq_zero_iff]
  lia

lemma C_pos_iff : 0 < C k j ↔ j ≤ k := by
  rw [← not_iff_not, not_lt, le_zero, C_eq_zero_iff, not_le]

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

theorem sum_range_C_mul (x y : ℤ) :
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

end

/-- The sequence of `n+3`-tuples providing a lower bound of `2n+1` on the quality
(i.e. `2n-5` for `n`-tuples where `n ≥ 3`). `k` moves between tuples and `i` is the tuple index. -/
def tup (n k : ℕ) (i : Fin (n + 3)) : ℤ :=
  i.lastCases 1 fun i' ↦
    i'.lastCases (-(2 ^ k) ^ (2 * n + 1)) fun j ↦
      C n j.1 * (2 ^ k - 1) ^ (2 * j.1 + 1) * (2 ^ k) ^ (n - j.1)

variable {n k : ℕ}

lemma tup_last : tup n k (Fin.last _) = 1 := by simp [tup]

lemma tup_second_last : tup n k (Fin.last _).castSucc = -(2 ^ k) ^ (2 * n + 1) := by simp [tup]

lemma tup_except_last_two {i : Fin (n + 1)} :
    tup n k i.castSucc.castSucc = C n i.1 * (2 ^ k - 1) ^ (2 * i.1 + 1) * (2 ^ k) ^ (n - i.1) := by
  simp [tup]

lemma sum_tup : ∑ i, tup n k i = 0 := by
  rw [Fin.sum_univ_castSucc, tup_last, Fin.sum_univ_castSucc, tup_second_last]
  simp_rw [tup_except_last_two,
    Fin.sum_univ_eq_sum_range fun j ↦ (C n j : ℤ) * (2 ^ k - 1) ^ (2 * j + 1) * (2 ^ k) ^ (n - j)]
  conv_lhs =>
    enter [1, 1, 2, j]
    rw [sub_eq_add_neg]
    enter [2]
    rw [← mul_one (2 ^ k), ← neg_mul_neg]
  rw [← sum_range_C_mul, neg_one_pow_eq_ite]
  grind

lemma gcd_tup : univ.gcd (tup n k) = 1 := by
  rw [← insert_eq_of_mem (mem_univ (Fin.last (n + 2))), gcd_insert]
  simp [tup]

lemma tup_sign {i : Fin (n + 3)} (hk : k ≠ 0) :
    (tup n k i < 0 ↔ i = (Fin.last (n + 1)).castSucc) ∧
    (0 < tup n k i ↔ i ≠ (Fin.last (n + 1)).castSucc) := by
  cases i using Fin.lastCases with
  | last => simp [tup_last]; grind
  | cast i =>
    cases i using Fin.lastCases with
    | last => simp [tup_second_last]
    | cast i =>
      suffices (0 : ℤ) < (C n i.1) * (2 ^ k - 1) ^ (2 * i.1 + 1) * (2 ^ k) ^ (n - i.1) by
        simpa [this, tup_except_last_two] using this.le
      have : 0 < C n i.1 := by rw [C_pos_iff]; lia
      have : 0 < (2 : ℤ) ^ k - 1 := by
        rw [sub_pos]
        exact (one_lt_pow₀ one_lt_two hk)
      positivity

lemma SSC_tup (hk : k ≠ 0) : SSC (tup n k) := fun b n₁ n₂ ↦ by
  by_cases hb : (Fin.last (n + 1)).castSucc ∈ b
  · rw [← @sum_tup n k, ← sum_add_sum_compl b, Ne, left_eq_add, ← Ne]
    refine (sum_pos (fun i mi ↦ ?_) n₂).ne'
    rw [mem_compl] at mi
    rw [(tup_sign hk).2]
    exact (ne_of_mem_of_not_mem hb mi).symm
  · refine (sum_pos (fun i mi ↦ ?_) n₁).ne'
    rw [(tup_sign hk).2]
    exact ne_of_mem_of_not_mem mi hb

lemma tup_mem_nConjectureTuples (hk : k ≠ 0) : tup n k ∈ nConjectureTuples (n + 3) := by
  simp [nConjectureTuples, sum_tup, SSC_tup hk, gcd_tup]

lemma maxAbs_tup (hk : k ≠ 0) : maxAbs (tup n k) = (2 ^ k) ^ (2 * n + 1) := by
  sorry

end BB94

#eval BB94.tup 1 2 -- ![36, 27, -64, 1]

/-- Theorem 1.3 in the paper, Browkin and Brzeziński (1994). -/
lemma le_quality_nConjectureTuples {n : ℕ} (hn : 3 ≤ n) :
    (2 * n - 5 : ℕ) ≤ quality (nConjectureTuples n) := by
  sorry
