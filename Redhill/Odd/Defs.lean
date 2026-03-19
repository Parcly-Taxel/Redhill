module

public import Redhill.Common.VWPair

@[expose] public section

namespace OddCase

open Nat Finset

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

lemma sum_tup : ∑ i, tup n F x i = 0 := by
  simp only [tup, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_five,
    add_assoc, show (x - 1) ^ 5 + (10 * (x ^ 2 + 1) ^ 2 + -(x + 1) ^ 5) = 8 by ring]
  rw [← add_assoc _ _ 8, ← sub_eq_add_neg, ← neg_sub, ← cast_sub (VW n F).ineq_chain.2.1,
    ← (VW n F).u_eq_sub, Fin.sum_univ_eq_sum_range (f := fun i ↦ (primeChain _ i : ℤ))]
  norm_num [U]

end OddCase
