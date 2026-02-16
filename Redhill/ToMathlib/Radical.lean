import Mathlib.RingTheory.Radical

/-- The radical of a natural number is the product of its prime factors.
This is computable, unlike `UniqueFactorizationMonoid.radical`. -/
def Nat.radical (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

variable {m n : ℕ}

lemma UniqueFactorizationMonoid.radical_eq_natRadical :
    UniqueFactorizationMonoid.radical n = n.radical := by
  simp [Nat.radical, radical, UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors]

namespace Nat

lemma natRadical_pos : 0 < n.radical := by
  rw [← UniqueFactorizationMonoid.radical_eq_natRadical]
  exact n.radical_pos

lemma one_lt_natRadical_iff : 1 < n.radical ↔ 1 < n := by
  rw [← UniqueFactorizationMonoid.radical_eq_natRadical, one_lt_radical_iff]

lemma radical_pow (hm : m ≠ 0) : (n ^ m).radical = n.radical := by
  simp_rw [← UniqueFactorizationMonoid.radical_eq_natRadical]
  exact UniqueFactorizationMonoid.radical_pow _ hm

lemma radical_dvd_self : n.radical ∣ n := by
  simp_rw [← UniqueFactorizationMonoid.radical_eq_natRadical]
  exact UniqueFactorizationMonoid.radical_dvd_self

lemma radical_mul_dvd : (m * n).radical ∣ m.radical * n.radical := by
  simp_rw [← UniqueFactorizationMonoid.radical_eq_natRadical]
  exact UniqueFactorizationMonoid.radical_mul_dvd

end Nat
