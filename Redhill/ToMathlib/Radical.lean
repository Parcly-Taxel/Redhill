import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Radical

/-- The radical of a natural number is the product of its prime factors.
This is computable, unlike `UniqueFactorizationMonoid.radical`. -/
def Nat.radical (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p

variable {m n : ℕ} {z : ℤ}

namespace UniqueFactorizationMonoid

lemma radical_eq_natRadical : radical n = n.radical := by
  simp [Nat.radical, radical, UniqueFactorizationMonoid.primeFactors_eq_natPrimeFactors]

lemma int_primeFactors_eq : primeFactors z = z.natAbs.primeFactors.map ⟨_, Nat.cast_injective⟩ := by
  obtain rfl | hz := eq_or_ne z 0; · simp
  ext p
  rw [mem_primeFactors, mem_normalizedFactors_iff' hz, irreducible_iff_prime,
    Int.nonneg_iff_normalize_eq_self]
  refine ⟨fun ⟨pp, nnp, dp⟩ ↦ ?_, fun h ↦ ?_⟩
  · lift p to ℕ using nnp
    rw [← Nat.prime_iff_prime_int] at pp
    rw [Int.natCast_dvd] at dp
    rw [Finset.mem_map]
    exact ⟨p, by simp_all, rfl⟩
  · simp_rw [Finset.mem_map, Function.Embedding.coeFn_mk, Nat.mem_primeFactors,
      Ne, Int.natAbs_eq_zero] at h
    obtain ⟨n, ⟨pn, dn, -⟩, rfl⟩ := h
    rw [Int.natCast_dvd, ← Nat.prime_iff_prime_int]
    exact ⟨pn, by simp, dn⟩

lemma radical_eq_intRadical : radical z = z.natAbs.radical := by
  change ∏ p ∈ primeFactors z, p = ∏ p ∈ z.natAbs.primeFactors, p
  simp [int_primeFactors_eq]

end UniqueFactorizationMonoid

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

namespace Int

open UniqueFactorizationMonoid

lemma radical_pos : 0 < radical z := by
  rw [radical_eq_intRadical, natCast_pos]
  exact Nat.natRadical_pos

lemma one_lt_radical_iff : 1 < radical z ↔ 1 < z.natAbs := by
  rw [radical_eq_intRadical, Nat.one_lt_cast]
  exact Nat.one_lt_natRadical_iff

end Int
