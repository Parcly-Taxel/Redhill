module

public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Redhill.Common.PairwiseCoprime
public import Redhill.Common.VWPair
public import Redhill.ToMathlib.Coprime

@[expose] public section

namespace OddCase

open Nat Fin Finset

/-- `primeChain s` is the lexicographically earliest sequence of primes
with `primeChain s 0 > s` and each succeeding element more than twice the last. -/
def primeChain (s : ℕ) : ℕ → ℕ
  | 0 => Nat.find (exists_infinite_primes (s + 1))
  | n + 1 => Nat.find (exists_infinite_primes (2 * primeChain s n + 1))

lemma prime_primeChain {s n : ℕ} : (primeChain s n).Prime := by
  induction n <;> exact (Nat.find_spec (exists_infinite_primes _)).2

lemma primeChain_zero_gt {s : ℕ} : s < primeChain s 0 :=
  (Nat.find_spec (exists_infinite_primes _)).1

lemma primeChain_succ_gt {s n : ℕ} : 2 * primeChain s n < primeChain s (n + 1) :=
  (Nat.find_spec (exists_infinite_primes _)).1

lemma strictMono_primeChain {s : ℕ} : StrictMono (primeChain s) :=
  strictMono_nat_of_lt_succ (by grind [primeChain_succ_gt])

variable (n : ℕ) (F : Finset ℕ)

/-- The sum of `tup` over all indices save `n` and `n + 1`, i.e. the input `u` to `VWPair`. -/
def U : ℕ := 8 + ∑ i ∈ range n, primeChain (2 * (F.sup id + 8)) i

/-- The `VWPair` generated from the inputs `u = m = U n F`. -/
def VW : VWPair (U n F) (U n F) := .ofUM _ _ (by grind [U]) (by grind [U])

/-- We require `x` in `tup` to be a multiple of this number,
an optimised version of the paper's `y`. -/
def Y : ℕ :=
  10 * F.prod id * (∏ i ∈ range n, primeChain (2 * (F.sup id + 8)) i) * (VW n F).v * (VW n F).w

/-- The `(n + 5)`-tuple for fixed `n, F` that for infinitely many `x`
belongs to `factorFreeTuples F n` **and** has quality tending to `5 / 3`,
assuming `n` is odd and `0, 1, 2, 5, 10 ∉ F`. -/
def tup (x : ℤ) (i : Fin (n + 5)) : ℤ :=
  i.addCases (primeChain (2 * (F.sup id + 8)) ·.1) fun
    | 0 => (VW n F).v
    | 1 => -(VW n F).w
    | 2 => (x - 1) ^ 5
    | 3 => 10 * (x ^ 2 + 1) ^ 2
    | 4 => -(x + 1) ^ 5

variable {n F} {x : ℤ}

@[simp] lemma tup_castAdd {i : Fin n} :
    tup n F x (i.castAdd 5) = primeChain (2 * (F.sup id + 8)) i.1 := by
  simp [tup]

@[simp] lemma tup_natAdd_zero : tup n F x (natAdd n 0) = (VW n F).v := by
  simp [tup]

@[simp] lemma tup_natAdd_one : tup n F x (natAdd n 1) = -(VW n F).w := by
  simp [tup]

@[simp] lemma tup_natAdd_two : tup n F x (natAdd n 2) = (x - 1) ^ 5 := by
  simp [tup]

@[simp] lemma tup_natAdd_three : tup n F x (natAdd n 3) = 10 * (x ^ 2 + 1) ^ 2 := by
  simp [tup]

@[simp] lemma tup_natAdd_four : tup n F x (natAdd n 4) = -(x + 1) ^ 5 := by
  simp [tup]

lemma sum_tup : ∑ i, tup n F x i = 0 := by
  simp only [tup, sum_univ_add, addCases_left, addCases_right, sum_univ_five,
    add_assoc, show (x - 1) ^ 5 + (10 * (x ^ 2 + 1) ^ 2 + -(x + 1) ^ 5) = 8 by ring]
  rw [← add_assoc _ _ 8, ← sub_eq_add_neg, ← neg_sub, ← cast_sub (VW n F).ineq_chain.2.1,
    ← (VW n F).u_eq_sub, sum_univ_eq_sum_range (f := fun i ↦ (primeChain _ i : ℤ))]
  norm_num [U]

section Coprime

variable {i : Fin n}

lemma primeChain_lt_U : primeChain (2 * (F.sup id + 8)) i.1 < U n F :=
  (single_le_sum_of_canonicallyOrdered (by simp_all)).trans_lt (lt_add_of_pos_left _ (by decide))

lemma sixteen_lt_primeChain : 16 < primeChain (2 * (F.sup id + 8)) n :=
  calc
    _ ≤ _ := by lia
    _ < _ := primeChain_zero_gt
    _ ≤ _ := strictMono_primeChain.monotone (Nat.zero_le _)

lemma primeChain_mem_Icc : primeChain (2 * (F.sup id + 8)) i.1 ∈ Icc 3 (U n F) :=
  mem_Icc.mpr ⟨sixteen_lt_primeChain.trans' (by decide), primeChain_lt_U.le⟩

lemma dvd_of_Y_dvd (dx : ↑(Y n F) ∣ x) :
    10 ∣ x ∧ (∀ f ∈ F, ↑f ∣ x) ∧ (∀ i : Fin n, ↑(primeChain (2 * (F.sup id + 8)) i.1) ∣ x) ∧
    ↑(VW n F).v ∣ x ∧ ↑(VW n F).w ∣ x := by
  simp_rw [Y, cast_mul, cast_ofNat, cast_prod, id_eq] at dx
  simp_rw [← and_assoc]
  iterate 2
    refine ⟨?_, dvd_of_mul_left_dvd dx⟩
    replace dx := dvd_of_mul_right_dvd dx
  refine ⟨?_, fun i ↦ ?_⟩
  · replace dx := dvd_of_mul_right_dvd dx
    exact ⟨dvd_of_mul_right_dvd dx,
      fun f mf ↦ (dvd_prod_of_mem _ mf).trans (dvd_of_mul_left_dvd dx)⟩
  · refine dvd_trans ?_ (dvd_of_mul_left_dvd dx)
    rw [← Fin.prod_univ_eq_prod_range]
    exact dvd_prod_of_mem _ (mem_univ _)

lemma isCoprime_tup_castAdd_natAdd {j : Fin 5} (dx : ↑(Y n F) ∣ x) :
    IsCoprime (tup n F x (castAdd 5 i)) (tup n F x (natAdd n j)) := by
  rw [tup_castAdd]
  replace dx := (dvd_of_Y_dvd dx).2.2.1
  fin_cases j <;> simp only [reduceFinMk]
  · rw [tup_natAdd_zero, isCoprime_iff_coprime, prime_primeChain.coprime_iff_not_dvd]
    exact ((VW n F).not_dvd _ primeChain_mem_Icc).1
  · rw [tup_natAdd_one, IsCoprime.neg_right_iff, isCoprime_iff_coprime,
      prime_primeChain.coprime_iff_not_dvd]
    exact ((VW n F).not_dvd _ primeChain_mem_Icc).2
  · rw [tup_natAdd_two, IsCoprime.pow_right_iff (by decide)]
    exact IsCoprime.sub_one_right_of_dvd (dx _)
  · rw [tup_natAdd_three, IsCoprime.mul_right_iff, IsCoprime.pow_right_iff zero_lt_two]
    constructor
    · norm_cast
      exact coprime_of_lt_prime (by decide) (by grind [sixteen_lt_primeChain]) prime_primeChain
    · exact IsCoprime.add_one_right_of_dvd (dvd_pow (dx i) two_ne_zero)
  · rw [tup_natAdd_four, IsCoprime.neg_right_iff, IsCoprime.pow_right_iff (by decide)]
    exact IsCoprime.add_one_right_of_dvd (dx _)

/-- This lemma is where we need evenness of `n`, i.e. oddness of the whole tuple's length. -/
lemma V_coprime_ten (hn : Even n) : (VW n F).v.Coprime 10 := by
  rw [show 10 = 2 * 5 by rfl]
  apply Coprime.mul_right
  · rw [coprime_two_right]
    have key : Even (U n F) := by
      apply Even.add (by decide)
      simp_rw [even_sum_iff_even_card_odd, prime_primeChain.odd_iff]
      have (i : ℕ) : 3 ≤ primeChain (2 * (F.sup id + 8)) i :=
        sixteen_lt_primeChain.le.trans' (by decide)
      simpa [this]
    rw [(VW n F).u_eq_sub, even_sub (VW n F).ineq_chain.2.1, ← not_iff_not, not_even_iff_odd,
      not_even_iff_odd] at key
    rw [← key]
    exact (VW n F).w_odd
  · rw [coprime_comm, prime_five.coprime_iff_not_dvd]
    exact ((VW n F).not_dvd 5 (mem_Icc.mpr ⟨by decide, by grind [U]⟩)).1

lemma W_coprime_ten : (VW n F).w.Coprime 10 := by
  rw [show 10 = 2 * 5 by rfl]
  apply Coprime.mul_right
  · rw [coprime_two_right]
    exact (VW n F).w_odd
  · rw [coprime_comm, prime_five.coprime_iff_not_dvd]
    exact ((VW n F).not_dvd 5 (mem_Icc.mpr ⟨by decide, by grind [U]⟩)).2

lemma pairwiseCoprime_tup (hn : Even n) (dx : ↑(Y n F) ∣ x) : PairwiseCoprime (tup n F x) := by
  refine Pairwise.of_lt (fun _ _ h ↦ h.symm) fun i j h ↦ ?_
  cases i using Fin.addCases <;> cases j using Fin.addCases
  case left.left i j =>
    simp only [tup_castAdd, isCoprime_iff_coprime]
    rw [coprime_primes prime_primeChain prime_primeChain]
    exact (strictMono_primeChain h).ne
  case left.right i j => exact isCoprime_tup_castAdd_natAdd dx
  case right.left i j => grind
  case right.right i j =>
    rw [natAdd_lt_natAdd_iff] at h
    obtain ⟨d10, -, -, dv, dw⟩ := dvd_of_Y_dvd dx
    have d2 : 2 ∣ x := dvd_trans (by decide) d10
    have cp2 := IsCoprime.add_one_sub_one_of_even (dvd_pow d2 two_ne_zero)
    rw [show x ^ 2 - 1 = (x + 1) * (x - 1) by ring, IsCoprime.mul_right_iff] at cp2
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by lia
    · rw [tup_natAdd_zero]
      obtain rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by lia
      · rw [tup_natAdd_one, IsCoprime.neg_right_iff, isCoprime_iff_coprime]
        exact (VW n F).coprime_of_le (by grind [U]) (by grind [U])
      · rw [tup_natAdd_two]
        exact (IsCoprime.sub_one_right_of_dvd dv).pow_right
      · rw [tup_natAdd_three, IsCoprime.mul_right_iff]
        refine ⟨?_, (IsCoprime.add_one_right_of_dvd (dvd_pow dv two_ne_zero)).pow_right⟩
        exact_mod_cast V_coprime_ten hn
      · rw [tup_natAdd_four]
        exact (IsCoprime.add_one_right_of_dvd dv).pow_right.neg_right
    · rw [tup_natAdd_one, IsCoprime.neg_left_iff]
      obtain rfl | rfl | rfl : j = 2 ∨ j = 3 ∨ j = 4 := by lia
      · rw [tup_natAdd_two]
        exact (IsCoprime.sub_one_right_of_dvd dw).pow_right
      · rw [tup_natAdd_three, IsCoprime.mul_right_iff]
        refine ⟨?_, (IsCoprime.add_one_right_of_dvd (dvd_pow dw two_ne_zero)).pow_right⟩
        exact_mod_cast W_coprime_ten
      · rw [tup_natAdd_four]
        exact (IsCoprime.add_one_right_of_dvd dw).pow_right.neg_right
    · rw [tup_natAdd_two, IsCoprime.pow_left_iff (by decide)]
      obtain rfl | rfl : j = 3 ∨ j = 4 := by lia
      · rw [tup_natAdd_three, IsCoprime.mul_right_iff]
        exact ⟨IsCoprime.sub_one_left_of_dvd d10, (cp2.2.symm).pow_right⟩
      · rw [tup_natAdd_four]
        exact (IsCoprime.add_one_sub_one_of_even d2).symm.pow_right.neg_right
    · obtain rfl : j = 4 := by lia
      rw [tup_natAdd_three, tup_natAdd_four, IsCoprime.neg_right_iff,
        IsCoprime.pow_right_iff (by decide), IsCoprime.mul_left_iff]
      exact ⟨IsCoprime.add_one_right_of_dvd d10, cp2.1.pow_left⟩

lemma lt_primeChain_of_mem_F {f : ℕ} (hf : f ∈ F) : f < primeChain (2 * (F.sup id + 8)) i.1 :=
  calc
    _ ≤ F.sup id := le_sup hf
    _ < _ := by lia
    _ < _ := primeChain_zero_gt
    _ ≤ _ := strictMono_primeChain.monotone (Nat.zero_le _)

lemma not_dvd_tup (dF : Disjoint {0, 1, 2, 5, 10} F) (f : ℕ) (hf : f ∈ F) (i : Fin (n + 5)) :
    ¬↑f ∣ tup n F x i := by
  have lf : 3 ≤ f := by grind
  cases i using Fin.addCases with
  | left i =>
    rw [tup_castAdd]
    norm_cast
    sorry
  | right i =>
    sorry

end Coprime

end OddCase
