module

public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.NumberTheory.Bertrand

/-!
The paper stipulates `u < 0 < m` and `w ≤ 0 < v`.
These bounds are formalised by typing all four variables as natural numbers,
negating `u` and `w` as needed.

The bound `w ≤ (m + 1) * primorial m` in the paper can also be sharpened to `w ≤ 4 * primorial m`
by applying the Chinese remainder theorem.

Note that the paper's algorithm does not necessarily guarantee `q < v` (without the negations
performed in this file). For example, take `m = 5, q = 30, u = -2`, then step 1 sets
`v = 29, w = -31` and both numbers are unchanged in the rest of the algorithm
because 29 and 31 are big primes.
-/

@[expose] public section

open Nat Finset

/-- `VWPair u m` holds `v` and `w` and states that `-u, m, v, -w` satisfy the conditions
in Lemma 2.2. -/
structure VWPair (u m : ℕ) where
  /-- `v` in the paper -/
  v : ℕ
  /-- `w` in the paper, **negated** -/
  w : ℕ
  /-- `u = v + w` in the paper -/
  u_eq_sub : u = w - v
  /-- The inequality chain bounding `v` and `w` -/
  ineq_chain : primorial m < v ∧ v ≤ w ∧ w ≤ 4 * primorial m
  /-- `gcd(v,w) = 1` -/
  coprime : v.Coprime w
  /-- No number in `[3,m]` divides `v` or `w` -/
  not_dvd (k) (hk : k ∈ Icc 3 m) : ¬k ∣ v ∧ ¬k ∣ w
  /-- `w` is odd -/
  w_odd : Odd w

namespace VWPair

lemma nonempty_double_not_dvd (v w p : ℕ) (hp : 3 ≤ p) :
    Finset.Nonempty {i : Fin p | ¬p ∣ v + i ∧ ¬p ∣ w + i} := by
  let nzp : NeZero p := ⟨by lia⟩
  have rearr (i : Fin p) (n : ℕ) : p ∣ n + i ↔ i = -Fin.ofNat p n := by
    rw [← add_eq_zero_iff_eq_neg, ← Fin.val_eq_zero_iff, Fin.val_add, Fin.val_ofNat,
      ← dvd_iff_mod_eq_zero]
    nth_rw 1 [← n.mod_add_div p, ← add_rotate, ← Nat.dvd_add_iff_left (by simp)]
  conv =>
    enter [1, 1, i]
    rw [rearr, rearr, ← not_or, ← @mem_singleton _ (-Fin.ofNat p w), ← mem_insert]
  rw [filter_notMem_eq_sdiff, ← card_pos, card_sdiff_of_subset (subset_univ _), Finset.card_univ,
    Fintype.card_fin]
  grind

/-- Note the divisor of 2 and not 4 for `w`. -/
lemma nonempty_double_not_dvd_four (v w : ℕ) :
    Finset.Nonempty {i : Fin 4 | ¬4 ∣ v + i ∧ ¬2 ∣ w + i} := by
  by_cases hw : 2 ∣ w
  · by_cases hv : v % 4 = 3
    · use 3; grind
    · use 1; grind
  · by_cases hv : 4 ∣ v
    · use 2; grind
    · use 0; grind

/-- The finset consisting of 4 and all odd primes at most `m`. -/
def fourAndOddPrimes (m : ℕ) : Finset ℕ :=
  insert 4 {p ∈ Icc 3 m | p.Prime}

lemma zero_notMem_fourAndOddPrimes {m : ℕ} : 0 ∉ fourAndOddPrimes m := by
  simp [fourAndOddPrimes]

lemma prod_fourAndOddPrimes_eq {m : ℕ} (hm : 2 ≤ m) :
    ∏ p ∈ fourAndOddPrimes m, p = 2 * primorial m := by
  have np4 : ¬Nat.Prime 4 := by decide
  rw [fourAndOddPrimes, prod_insert (by simp [np4]), show 4 = 2 * 2 by rfl, mul_assoc]
  congr
  let f := fun p ↦ if p.Prime then p else 1
  rw [prod_filter]
  change f 2 * ∏ p ∈ Icc 3 m, f p = _
  rw [← prod_insert (by simp), primorial]
  simp_rw [f, prod_filter]
  refine prod_subset (by grind) fun p mp np ↦ ?_
  obtain rfl | rfl : p = 0 ∨ p = 1 := by grind
  all_goals decide

lemma fourAndOddPrimes_pairwise_coprime {m : ℕ} : Set.Pairwise (fourAndOddPrimes m) Coprime := by
  rw [fourAndOddPrimes, coe_insert, coe_filter, Set.pairwise_insert_of_symmetric Coprime.symmetric]
  refine ⟨fun p mp q mq hn ↦ (coprime_primes mp.2 mq.2).mpr hn, fun p ⟨bp, pp⟩ _ ↦ ?_⟩
  rw [show 4 = 2 ^ 2 by rfl]
  apply Coprime.pow_left
  rw [coprime_two_left]
  exact pp.odd_of_ne_two (by grind)

/-- Produce a number `i < p` such that `v + i` and `w + i` are both not divisible by `p`.
When `p = 4`, `w + i` is additionally guaranteed to be odd. Return 0 for `p ≤ 2`. -/
def nonDividingShift (v w p : ℕ) : ℕ :=
  if p = 4 then (Finset.min' _ (nonempty_double_not_dvd_four v w)).1 else
  if hp : 3 ≤ p then (Finset.min' _ (nonempty_double_not_dvd v w p hp)).1 else 0

/-- `crtShift v w m` is a number less than `2 * primorial m` that can be added to `v, w` such that
* no number in `[3,m]` divides the resulting `v` or `w`
* the resulting `w` is odd.

This number is calculated through the Chinese remainder theorem. -/
def crtShift (v w m : ℕ) : ℕ :=
  chineseRemainderOfFinset (nonDividingShift v w) id (fourAndOddPrimes m)
    (by simp [zero_notMem_fourAndOddPrimes]) fourAndOddPrimes_pairwise_coprime

lemma crtShift_lt {v w m : ℕ} (hm : 2 ≤ m) : crtShift v w m < 2 * primorial m := by
  rw [← prod_fourAndOddPrimes_eq hm]
  exact chineseRemainderOfFinset_lt_prod ..

lemma crtShift_not_dvd {v w m k : ℕ} (hk : k ∈ Icc 3 m) :
    ¬k ∣ v + crtShift v w m ∧ ¬k ∣ w + crtShift v w m := by
  sorry

lemma le_primorial_self {m : ℕ} : m ≤ primorial m := by
  rcases lt_or_ge m 3 with hm | hm
  · obtain rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 := by lia
    all_goals decide
  · suffices ∃ p ≥ 3, p.Prime ∧ p ≤ m ∧ m ≤ 2 * p by
      obtain ⟨p, pp, bnd⟩ := this
      apply bnd.2.2.trans
      have rearr : 2 * p = ∏ q ∈ {2, p} with q.Prime, q := by
        rw [prod_filter, prod_insert (by grind), prod_singleton]
        simp [bnd.1, prime_two]
      rw [rearr, primorial, prod_filter, prod_filter]
      refine prod_le_prod_of_subset_of_one_le' (by grind) fun q _ _ ↦ ?_
      split_ifs with hq
      · exact hq.one_le
      · rfl
    obtain ⟨p, pp, bp₁, bp₂⟩ := bertrand ((m + 1) / 2) (by lia)
    refine ⟨p, by lia, pp, ?_, by lia⟩
    suffices p ≠ 2 * ((m + 1) / 2) by lia
    contrapose pp
    subst pp
    exact not_prime_mul (by decide) (by lia)

/-- Lemma 2.2. When `0 < u` and `max 2 u ≤ m`, we can construct a `VWPair u m`. -/
def ofUM {u m : ℕ} (hu : u ≠ 0) (hm : max 2 u ≤ m) : VWPair u m where
  v := primorial m + 1 + crtShift (primorial m + 1) (primorial m + 1 + u) m
  w := primorial m + 1 + u + crtShift (primorial m + 1) (primorial m + 1 + u) m
  u_eq_sub := by lia
  ineq_chain := by
    refine ⟨by lia, by lia, ?_⟩
    rw [max_le_iff] at hm
    grind [le_primorial_self, @crtShift_lt (primorial m + 1) (primorial m + 1 + u) _ hm.1]
  coprime := by
    sorry
  not_dvd k hk := crtShift_not_dvd hk
  w_odd := by
    sorry

end VWPair
