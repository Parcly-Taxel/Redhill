module

public import Redhill.Common.PairwiseCoprime
public import Redhill.Common.VWPair

@[expose] public section

namespace OddCase

open Nat Fin Finset

/-- `primeChain s` is the lexicographically earliest sequence of primes
with `primeChain s 0 > s` and each succeeding element more than 3 times the last. -/
def primeChain (s : ℕ) : ℕ → ℕ
  | 0 => Nat.find (exists_infinite_primes (s + 1))
  | n + 1 => Nat.find (exists_infinite_primes (3 * primeChain s n + 1))

lemma prime_primeChain {s n : ℕ} : (primeChain s n).Prime := by
  induction n <;> exact (Nat.find_spec (exists_infinite_primes _)).2

lemma primeChain_zero_gt {s : ℕ} : s < primeChain s 0 :=
  (Nat.find_spec (exists_infinite_primes _)).1

lemma primeChain_succ_gt {s n : ℕ} : 3 * primeChain s n < primeChain s (n + 1) :=
  (Nat.find_spec (exists_infinite_primes _)).1

lemma strictMono_primeChain {s : ℕ} : StrictMono (primeChain s) :=
  strictMono_nat_of_lt_succ (by grind [primeChain_succ_gt])

variable (n : ℕ) (F : Finset ℕ)

/-- The sum of `tup` over all indices save `n` and `n + 1`, i.e. the input `u` to `VWPair`. -/
def U : ℕ := 8 + ∑ i ∈ range n, primeChain (3 * (F.sup id + 8)) i

/-- The `VWPair` generated from the inputs `u = m = U n F`. -/
def VW : VWPair (U n F) (U n F) := .ofUM _ _ (by grind [U]) (by grind [U])

/-- We require `x` in `tup` to be a multiple of this number,
an optimised version of the paper's `y`. -/
def Y : ℕ :=
  10 * F.prod id * (∏ i ∈ range n, primeChain (3 * (F.sup id + 8)) i) * (VW n F).v * (VW n F).w

/-- The `(n + 5)`-tuple for fixed `n, F` that for infinitely many `x`
belongs to `factorFreeTuples F n` **and** has quality tending to `5 / 3`,
assuming `n` is odd and `0, 1, 2, 5, 10 ∉ F`. -/
def tup (x : ℤ) (i : Fin (n + 5)) : ℤ :=
  i.addCases (primeChain (3 * (F.sup id + 8)) ·.1) fun
    | 0 => (VW n F).v
    | 1 => -(VW n F).w
    | 2 => (x - 1) ^ 5
    | 3 => 10 * (x ^ 2 + 1) ^ 2
    | 4 => -(x + 1) ^ 5

variable {n F} {x : ℤ}

@[simp] lemma tup_castAdd {i : Fin n} :
    tup n F x (i.castAdd 5) = primeChain (3 * (F.sup id + 8)) i.1 := by
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

/-
lemma isCoprime_tup_castAdd {i j : Fin n} (h : i < j) :
    IsCoprime (tup n F x (castAdd 5 i)) (tup n F x (castAdd 5 j)) := by
  simp only [tup_castAdd, isCoprime_iff_coprime]
  rw [coprime_primes prime_primeChain prime_primeChain]
  sorry
-/

lemma pairwiseCoprime_tup (dx : ↑(Y n F) ∣ x) : PairwiseCoprime (tup n F x) := by
  refine Pairwise.of_lt (fun i j h ↦ h.symm) fun i j h ↦ ?_
  cases i using Fin.addCases with
  | left i =>
    cases j using Fin.addCases with
    | left j =>
      simp only [tup_castAdd, isCoprime_iff_coprime]
      rw [coprime_primes prime_primeChain prime_primeChain]
      exact (strictMono_primeChain h).ne
    | right j => sorry
  | right i =>
    sorry

end Coprime

end OddCase
