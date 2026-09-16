import OdlyzkoPoonen.Probability.ReciprocalDivisorNormalization
import OdlyzkoPoonen.Asymptotics.ReciprocalNoncyclotomic

/-!
# Reciprocal-divisor estimates with no normalization condition

The sign-normalization equivalence removes monicity from the witness in both
the exact finite estimate and the superpolynomial conclusion of Lemma 3.2.
The cyclotomic condition still concerns the original random polynomial.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics

lemma exists_unrestricted_reciprocal_finite_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
      binaryProbability (n - 1) (fun P ↦
        (∃ J : ℤ[X], J ∣ P ∧ J.reverse = J ∧ 1 ≤ J.natDegree) ∧
          ¬ HasCyclotomicDivisor P) ≤
        Real.exp (4 * (L : ℝ) ^ 2 - a * (n : ℝ) / Real.log (n : ℝ) ^ 4) +
          6 * (2 : ℝ) ^ (-(L : ℝ) / 2) := by
  simpa only [binaryProbability_reciprocal_noncyclotomic_unrestricted] using
    exists_noncyclotomic_reciprocal_finite_bound

lemma binaryProbability_unrestricted_reciprocal_noncyclotomic_isBigO
    (A : ℝ) (hA : 0 < A) :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun P ↦
      (∃ J : ℤ[X], J ∣ P ∧ J.reverse = J ∧ 1 ≤ J.natDegree) ∧
        ¬ HasCyclotomicDivisor P)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
  simpa only [binaryProbability_reciprocal_noncyclotomic_unrestricted] using
    binaryProbability_reciprocal_noncyclotomic_isBigO A hA

end OdlyzkoPoonen
