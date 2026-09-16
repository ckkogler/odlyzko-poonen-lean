import OdlyzkoPoonen.FiniteField.ReciprocalUnionBound
import OdlyzkoPoonen.Probability.ReciprocalTail

/-!
# The reciprocal gcd probability bound

The exact finite-family counts and fixed-divisor bounds give the probability
estimate for the actual gcd with the reversed polynomial. The exponent is real
halving, not truncated natural division. The result also includes threshold
zero, although the main application uses positive thresholds.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma f2Probability_gcd_degree_le {n : ℕ} (hn : 1 ≤ n) (L : ℕ) :
    f2Probability (n - 1)
      (fun p ↦ L ≤ (GCDMonoid.gcd p p.reverse).natDegree) ≤
      6 * (2 : ℝ) ^ (-(L : ℝ) / 2) :=
  (f2Probability_gcd_degree_le_sum hn L).trans (sum_reciprocal_counting_le_rpow L n)

/-- The finite-field gcd estimate under the original integer binary law. -/
theorem reciprocal_gcd_probability {n : ℕ} (hn : 1 ≤ n) (L : ℕ) :
    binaryProbability (n - 1) (fun p ↦
      L ≤ (GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse).natDegree) ≤
      6 * (2 : ℝ) ^ (-(L : ℝ) / 2) :=
  f2Probability_gcd_degree_le hn L

end OdlyzkoPoonen
