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

The coprimality condition is derived from the preconditions on `u, m`, not defined as a field
of `VWPair`, since said preconditions are light.
-/

@[expose] public section

open Nat Finset

/-- Upstreamable to mathlib! -/
lemma Nat.Prime.odd_iff {p : ℕ} (hp : p.Prime) : Odd p ↔ 3 ≤ p := by
  rw [← not_iff_not, not_odd_iff_even, hp.even_iff, not_le]
  grind [hp.two_le]

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
  /-- No number in `[3,m]` divides `v` or `w` -/
  not_dvd (k) (hk : k ∈ Icc 3 m) : ¬k ∣ v ∧ ¬k ∣ w
  /-- `w` is odd -/
  w_odd : Odd w

namespace VWPair

variable {v w u m p : ℕ}

/-- When the preconditions on `u` and `m` in Lemma 2.2 are satisfied, `v` and `w` are coprime. -/
lemma coprime_of_le (pair : VWPair u m) (hu : 0 < u) (hm : u ≤ m) :
    pair.v.Coprime pair.w := by
  by_contra h
  rw [Prime.not_coprime_iff_dvd] at h
  obtain ⟨p, pp, dv, dw⟩ := h
  obtain rfl | op := pp.eq_two_or_odd'
  · grind [pair.w_odd]
  rw [pp.odd_iff] at op
  obtain hp | hp := le_or_gt p m
  · exact (pair.not_dvd p (mem_Icc.mpr ⟨op, hp⟩)).1 dv
  grind [le_of_dvd hu (pair.u_eq_sub.symm ▸ dvd_sub dw dv)]

variable (v w p) in
lemma nonempty_double_not_dvd (hp : 3 ≤ p) :
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

variable (v w) in
/-- Note the divisor of 2 and not 4 for `w`. -/
lemma nonempty_double_not_dvd_four : Finset.Nonempty {i : Fin 4 | ¬4 ∣ v + i ∧ ¬2 ∣ w + i} := by
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

lemma zero_notMem_fourAndOddPrimes : 0 ∉ fourAndOddPrimes m := by
  simp [fourAndOddPrimes]

lemma prod_fourAndOddPrimes_eq (hm : 2 ≤ m) : ∏ p ∈ fourAndOddPrimes m, p = 2 * primorial m := by
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

lemma fourAndOddPrimes_pairwise_coprime : Set.Pairwise (fourAndOddPrimes m) Coprime := by
  rw [fourAndOddPrimes, coe_insert, coe_filter, Set.pairwise_insert_of_symmetric Coprime.symmetric]
  refine ⟨fun p mp q mq hn ↦ (coprime_primes mp.2 mq.2).mpr hn, fun p ⟨bp, pp⟩ _ ↦ ?_⟩
  rw [show 4 = 2 ^ 2 by rfl]
  apply Coprime.pow_left
  rw [coprime_two_left]
  exact pp.odd_of_ne_two (by grind)

/-- Produce a number `i < p` such that `v + i` and `w + i` are both not divisible by `p`.
When `p = 4`, `w + i` is additionally guaranteed to be odd. Return 0 for `p ≤ 2`. -/
def nonDividingShift (v w p : ℕ) : ℕ :=
  if p = 4 then (min' _ (nonempty_double_not_dvd_four v w)).1 else
  if hp : 3 ≤ p then (min' _ (nonempty_double_not_dvd v w p hp)).1 else 0

lemma not_dvd_nonDividingShift_of_three_le (hp : 3 ≤ p) :
    ¬p ∣ v + nonDividingShift v w p ∧ ¬p ∣ w + nonDividingShift v w p := by
  unfold nonDividingShift
  split_ifs with p4
  · subst p4
    obtain ⟨dv, dw⟩ := (mem_filter_univ _).mp (min'_mem _ (nonempty_double_not_dvd_four v w))
    refine ⟨dv, ?_⟩
    contrapose! dw
    exact (show 2 ∣ 4 by decide).trans dw
  simpa using min'_mem _ (nonempty_double_not_dvd v w p hp)

/-- `crtShift v w m` is a number less than `2 * primorial m` that can be added to `v, w` such that
* no number in `[3,m]` divides the resulting `v` or `w`
* the resulting `w` is odd.

This number is calculated through the Chinese remainder theorem. -/
def crtShift (v w m : ℕ) : ℕ :=
  chineseRemainderOfFinset (nonDividingShift v w) id (fourAndOddPrimes m)
    (by simp [zero_notMem_fourAndOddPrimes]) fourAndOddPrimes_pairwise_coprime

lemma crtShift_modEq (mi : p ∈ fourAndOddPrimes m) :
    crtShift v w m ≡ nonDividingShift v w p [MOD p] :=
  (chineseRemainderOfFinset ..).2 _ mi

lemma crtShift_lt (hm : 2 ≤ m) : crtShift v w m < 2 * primorial m := by
  rw [← prod_fourAndOddPrimes_eq hm]
  exact chineseRemainderOfFinset_lt_prod ..

lemma crtShift_not_dvd {k : ℕ} (hk : k ∈ Icc 3 m) :
    ¬k ∣ v + crtShift v w m ∧ ¬k ∣ w + crtShift v w m := by
  obtain ⟨i, rfl⟩ | ⟨p, pp, dp, op⟩ := eq_two_pow_or_exists_odd_prime_and_dvd k
  · rcases lt_or_ge i 2 with hi | hi
    · obtain rfl | rfl : i = 0 ∨ i = 1 := by lia
      all_goals grind
    suffices ¬4 ∣ v + crtShift v w m ∧ ¬4 ∣ w + crtShift v w m by
      contrapose this
      rw [← not_or, not_not] at this ⊢
      have d2i : 2 ^ 2 ∣ 2 ^ i := pow_dvd_pow_iff_le_right'.mpr hi
      exact this.imp (d2i.trans ·) (d2i.trans ·)
    have meq : crtShift v w m ≡ nonDividingShift v w 4 [MOD 4] := by
      simp [crtShift_modEq, fourAndOddPrimes]
    rw [dvd_iff_mod_eq_zero, add_mod, meq, ← add_mod, dvd_iff_mod_eq_zero, add_mod w, meq,
      ← add_mod, ← dvd_iff_mod_eq_zero, ← dvd_iff_mod_eq_zero]
    exact not_dvd_nonDividingShift_of_three_le (by decide)
  · suffices ¬p ∣ v + crtShift v w m ∧ ¬p ∣ w + crtShift v w m by
      contrapose this
      rw [← not_or, not_not] at this ⊢
      exact this.imp (dp.trans ·) (dp.trans ·)
    rw [mem_Icc] at hk
    rw [pp.odd_iff] at op
    have meq : crtShift v w m ≡ nonDividingShift v w p [MOD p] := by
      apply crtShift_modEq
      rw [fourAndOddPrimes, mem_insert, mem_filter, mem_Icc]
      refine .inr ⟨⟨op, ?_⟩, pp⟩
      exact (le_of_dvd (zero_lt_three.trans_le hk.1) dp).trans hk.2
    rw [dvd_iff_mod_eq_zero, add_mod, meq, ← add_mod, dvd_iff_mod_eq_zero, add_mod w, meq,
      ← add_mod, ← dvd_iff_mod_eq_zero, ← dvd_iff_mod_eq_zero]
    exact not_dvd_nonDividingShift_of_three_le op

lemma odd_add_crtShift : Odd (w + crtShift v w m) := by
  rw [← not_even_iff_odd, even_iff_two_dvd]
  have meq : crtShift v w m ≡ nonDividingShift v w 4 [MOD 2] := by
    apply ModEq.of_dvd (show 2 ∣ 4 by decide)
    simp [crtShift_modEq, fourAndOddPrimes]
  rw [dvd_iff_mod_eq_zero, add_mod, meq, ← add_mod, ← dvd_iff_mod_eq_zero]
  simp only [nonDividingShift, ↓reduceIte]
  have key := min'_mem _ (nonempty_double_not_dvd_four v w)
  simp_all

/-- Upstreamable to mathlib! -/
lemma le_primorial_self : m ≤ primorial m := by
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
def ofUM (hu : 0 < u) (hm : max 2 u ≤ m) : VWPair u m where
  v := primorial m + 1 + crtShift (primorial m + 1) (primorial m + 1 + u) m
  w := primorial m + 1 + u + crtShift (primorial m + 1) (primorial m + 1 + u) m
  u_eq_sub := by lia
  ineq_chain := by
    refine ⟨by lia, by lia, ?_⟩
    rw [max_le_iff] at hm
    grind [le_primorial_self, @crtShift_lt (primorial m + 1) (primorial m + 1 + u) _ hm.1]
  not_dvd k hk := crtShift_not_dvd hk
  w_odd := odd_add_crtShift

lemma ofUM_coprime (hu : 0 < u) (hm : max 2 u ≤ m) : (ofUM hu hm).v.Coprime (ofUM hu hm).w :=
  (ofUM hu hm).coprime_of_le hu (by simp_all)

end VWPair
