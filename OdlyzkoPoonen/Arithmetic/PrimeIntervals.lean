import Mathlib.NumberTheory.Chebyshev
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-!
# Exact products of the primes in an interval

The interval has an open lower endpoint and closed upper endpoint. Its
logarithmic product is the difference of the actual Chebyshev functions.
The product divides an integer if each of its primes does, since the primes
are distinct. Empty and reversed intervals are included in the definitions.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

/-- The distinct primes `p` satisfying `a < p <= b`. -/
def primesInInterval (a b : ℕ) : Finset ℕ := Nat.primesLE b \ Nat.primesLE a

/-- The actual integer product of all primes in the interval. -/
def primeIntervalProduct (a b : ℕ) : ℕ := ∏ p ∈ primesInInterval a b, p

lemma mem_primesInInterval {a b p : ℕ} :
    p ∈ primesInInterval a b ↔ p.Prime ∧ a < p ∧ p ≤ b := by
  simp only [primesInInterval, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hb, hp⟩, ha⟩
    exact ⟨hp, lt_of_not_ge (fun hpa ↦ ha ⟨hpa, hp⟩), hb⟩
  · rintro ⟨hp, ha, hb⟩
    exact ⟨⟨hb, hp⟩, by omega⟩

lemma primeIntervalProduct_pos (a b : ℕ) : 0 < primeIntervalProduct a b := by
  apply Finset.prod_pos
  intro p hp
  exact (mem_primesInInterval.mp hp).1.pos

lemma log_primeIntervalProduct {a b : ℕ} (hab : a ≤ b) :
    Real.log (primeIntervalProduct a b : ℝ) =
      Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) := by
  rw [primeIntervalProduct, Nat.cast_prod, Real.log_prod]
  · rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
    exact Finset.sum_sdiff_eq_sub (Nat.primesLE_mono hab)
  · intro p hp
    exact_mod_cast (mem_primesInInterval.mp hp).1.ne_zero

lemma primeIntervalProduct_dvd {a b B : ℕ}
    (hdiv : ∀ p ∈ primesInInterval a b, p ∣ B) : primeIntervalProduct a b ∣ B := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hne
    apply Nat.coprime_iff_isRelPrime.mp
    exact (Nat.coprime_primes (mem_primesInInterval.mp hp).1
      (mem_primesInInterval.mp hq).1).mpr hne
  · exact hdiv

lemma exists_prime_in_interval_not_dvd {a b B : ℕ} (hB : 0 < B)
    (hprod : B < primeIntervalProduct a b) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b ∧ ¬ p ∣ B := by
  by_contra! h
  have hd : primeIntervalProduct a b ∣ B := primeIntervalProduct_dvd (fun p hp ↦
    h p (mem_primesInInterval.mp hp).1 (mem_primesInInterval.mp hp).2.1
      (mem_primesInInterval.mp hp).2.2)
  exact (not_lt_of_ge (Nat.le_of_dvd hB hd)) hprod

end OdlyzkoPoonen
