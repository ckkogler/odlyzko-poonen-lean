import OdlyzkoPoonen.Polynomial.ReciprocalDivisorReduction
import OdlyzkoPoonen.FiniteField.ReciprocalProbability

/-!
# Probability of a large reciprocal integer divisor

Every monic reciprocal integer divisor contributes its full degree to the
finite-field gcd after reduction. The gcd probability bound therefore also
controls the existence of any such divisor above a degree threshold. This
is the large-divisor input in the reciprocal-factor argument.
-/

namespace OdlyzkoPoonen
open Polynomial

/-- A monic reciprocal integer divisor of degree at least `L`. -/
def HasLargeReciprocalIntegerDivisor (L : ℕ) (p : ℤ[X]) : Prop :=
  ∃ J : ℤ[X], J.Monic ∧ J ∣ p ∧ J.reverse = J ∧ L ≤ J.natDegree

lemma HasBinaryEndpoints.gcd_degree_of_large_reciprocal_divisor {n L : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (h : HasLargeReciprocalIntegerDivisor L p) :
    L ≤ (GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse).natDegree := by
  obtain ⟨J, hJ, hdvd, hrec, hL⟩ := h
  exact hL.trans (hp.reciprocal_divisor_degree_le_gcd hJ hdvd hrec)

lemma binaryProbability_large_reciprocal_divisor_le {n : ℕ} (hn : 1 ≤ n) (L : ℕ) :
    binaryProbability (n - 1) (HasLargeReciprocalIntegerDivisor L) ≤
      6 * (2 : ℝ) ^ (-(L : ℝ) / 2) := by
  calc
    _ ≤ binaryProbability (n - 1) (fun p ↦
        L ≤ (GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse).natDegree) := by
      apply uniformProbability_mono
      intro w hw
      have hp := wordPolynomial_endpoints w
      rw [Nat.sub_add_cancel hn] at hp
      exact hp.gcd_degree_of_large_reciprocal_divisor hw
    _ ≤ _ := reciprocal_gcd_probability hn L

end OdlyzkoPoonen
