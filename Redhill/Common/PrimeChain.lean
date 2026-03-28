module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Prime.Infinite

@[expose] public section

open Nat

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
