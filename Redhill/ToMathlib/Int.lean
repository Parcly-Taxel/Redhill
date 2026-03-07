import Mathlib.Data.Int.Order.Basic

namespace Int

variable {a b : ℤ}

protected lemma mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rw [Int.lt_iff_le_and_ne, Int.mul_nonneg_iff, ne_comm, Int.mul_ne_zero_iff]
  lia

protected lemma mul_neg_iff : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  rw [← not_iff_not, not_lt, Int.mul_nonneg_iff]
  lia

protected lemma mul_nonpos_iff : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  rw [← not_iff_not, not_le, Int.mul_pos_iff]
  lia

end Int
