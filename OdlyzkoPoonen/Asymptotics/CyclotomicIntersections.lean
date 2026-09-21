import OdlyzkoPoonen.Polynomial.CyclotomicProducts
import OdlyzkoPoonen.Probability.PeriodicDivisorBound

/-!
# Decay bounds for cyclotomic intersections

The sum of the degrees controls the probability of a simultaneous collection
of distinct cyclotomic divisors. In particular the pair intersections among
orders 3, 4 and 6 are all of quadratic order.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics
open scoped BigOperators Classical

theorem binaryProbability_cyclotomic_intersection_isBigO
    (s : Finset ℕ) (hs : ∀ k ∈ s, 0 < k) (R : ℕ)
    (hdegree : 2 * R ≤ ∑ k ∈ s, k.totient) :
    (fun n : ℕ ↦ binaryProbability (n - 1)
      (fun p ↦ ∀ k ∈ s, cyclotomic k ℤ ∣ p)) =O[atTop]
      (fun n : ℕ ↦ ((n : ℝ) ^ R)⁻¹) := by
  obtain ⟨hl, hd⟩ := cyclotomicProduct_common_period hs
  have h := binaryProbability_periodic_divisor_isBigO hl (cyclotomicProduct_monic s).ne_zero hd
    (by simpa only [cyclotomicProduct_natDegree] using hdegree)
  simpa only [cyclotomicProduct_dvd_iff hs] using h

theorem binaryProbability_cyclotomic_pair_isBigO {k l R : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hkl : k ≠ l) (hdegree : 2 * R ≤ k.totient + l.totient) :
    (fun n : ℕ ↦ binaryProbability (n - 1)
      (fun p ↦ cyclotomic k ℤ ∣ p ∧ cyclotomic l ℤ ∣ p)) =O[atTop]
      (fun n : ℕ ↦ ((n : ℝ) ^ R)⁻¹) := by
  have hs : ∀ j ∈ ({k, l} : Finset ℕ), 0 < j := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact hk
    · exact hl
  have hd : 2 * R ≤ ∑ j ∈ ({k, l} : Finset ℕ), j.totient := by simpa [hkl] using hdegree
  simpa only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    using binaryProbability_cyclotomic_intersection_isBigO {k, l} hs R hd

end OdlyzkoPoonen
