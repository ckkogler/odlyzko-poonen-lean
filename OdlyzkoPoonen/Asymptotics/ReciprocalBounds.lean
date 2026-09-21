import OdlyzkoPoonen.FiniteField.ReciprocalProbability
import OdlyzkoPoonen.Asymptotics.ReciprocalDivisorNormalization

/-!
# Reciprocal-divisor estimates with coefficient eight

These forms follow from the stronger coefficient-six estimates. All exponents
use real division, including odd cutoffs.
-/

namespace OdlyzkoPoonen
open Polynomial

/-- A coefficient-eight bound for the degree of the reciprocal gcd. -/
theorem reciprocal_gcd_probability_le_eight {n : ℕ} (hn : 1 ≤ n) (L : ℕ) :
    binaryProbability (n - 1) (fun p ↦
      L ≤ (GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse).natDegree) ≤
      8 * (2 : ℝ) ^ (-(L : ℝ) / 2) := by
  have h := reciprocal_gcd_probability hn L
  have hp := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(L : ℝ) / 2)
  linarith

/-- One constant and degree threshold work for every reciprocal-divisor cutoff. -/
theorem exists_unrestricted_reciprocal_finite_bound_eight :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
      binaryProbability (n - 1) (fun P ↦
        (∃ J : ℤ[X], J ∣ P ∧ J.reverse = J ∧ 1 ≤ J.natDegree) ∧
          ¬ HasCyclotomicDivisor P) ≤
        Real.exp (4 * (L : ℝ) ^ 2 - a * (n : ℝ) / Real.log (n : ℝ) ^ 4) +
          8 * (2 : ℝ) ^ (-(L : ℝ) / 2) := by
  obtain ⟨a, ha, N, hN, h⟩ := exists_unrestricted_reciprocal_finite_bound
  refine ⟨a, ha, N, hN, ?_⟩
  intro n hn L
  have hb := h n hn L
  have hp := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(L : ℝ) / 2)
  linarith

end OdlyzkoPoonen
