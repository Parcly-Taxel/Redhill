module

public import Mathlib.NumberTheory.Primorial

/-!
The paper stipulates `u < 0 < m` and `w ≤ 0 < v`.
These bounds are formalised by typing all four variables as natural numbers,
negating `u` and `w` as needed.
-/

@[expose] public section

open Finset

/-- `VWPair u m` holds `v` and `w` and states that `-u, m, v, -w` satisfy the conditions
in Lemma 2.2. -/
structure VWPair (u m : ℕ) where
  /-- `v` in the paper -/
  v : ℕ
  /-- `w` in the paper, **negated** -/
  w : ℕ
  /-- `w` is odd -/
  w_odd : Odd w
  /-- `u = v + w` in the paper -/
  u_eq_sub : u = w - v
  /-- The inequality chain bounding `v` and `w` -/
  ineq_chain : primorial m < v ∧ v ≤ w ∧ w ≤ (m + 1) * primorial m
  /-- `gcd(v,w) = 1` -/
  coprime : v.Coprime w
  /-- No number in `[3,m]` divides `v` or `w` -/
  not_dvd : ∀ k ∈ Icc 3 m, ¬k ∣ v ∧ ¬k ∣ w
