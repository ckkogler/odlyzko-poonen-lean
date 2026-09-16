import OdlyzkoPoonen.Polynomial.ReciprocalDivisorReduction
import OdlyzkoPoonen.FiniteField.DivisorCounting

/-!
# A fixed monic integer divisor is exponentially unlikely in its degree

If a monic polynomial divides one of the binary samples, its constant coefficient
is one by the proved factor-reversal argument. Otherwise its divisibility event
is empty. In the remaining case, monic reduction modulo two preserves the degree
and gives the established finite-field counting bound. No reciprocal or binary
coefficient condition is imposed on the fixed divisor.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma binaryProbability_divisible_eq_zero_of_constant (m : ℕ) {J : ℤ[X]}
    (hJ : J.Monic) (h0 : J.coeff 0 ≠ 1) :
    binaryProbability m (fun p ↦ J ∣ p) = 0 := by
  have hf (w : Fin m → Bool) : ¬ J ∣ wordPolynomial w := by
    intro hd
    exact h0 ((wordPolynomial_endpoints w).monic_divisor_constant hJ hd)
  simp [binaryProbability, uniformProbability, hf]

lemma binaryProbability_divisible_eq_zero_of_degree {n : ℕ} (hn : 1 ≤ n)
    {J : ℤ[X]} (hdegree : n < J.natDegree) :
    binaryProbability (n - 1) (fun p ↦ J ∣ p) = 0 := by
  have hf (w : Fin (n - 1) → Bool) : ¬ J ∣ wordPolynomial w := by
    intro hd
    have hle := natDegree_le_of_dvd hd (wordPolynomial_endpoints w).ne_zero
    rw [natDegree_wordPolynomial, Nat.sub_add_cancel hn] at hle
    omega
  simp [binaryProbability, uniformProbability, hf]

lemma binaryProbability_monic_divisible_le {n : ℕ} (hn : 1 ≤ n)
    {J : ℤ[X]} (hJ : J.Monic) :
    binaryProbability (n - 1) (fun p ↦ J ∣ p) ≤ 2 / (2 : ℝ) ^ J.natDegree := by
  by_cases h0 : J.coeff 0 = 1
  · have hred : HasF2Endpoints J.natDegree (reducePolynomial 2 J) := by
      refine ⟨hJ.map _, monic_reduce_natDegree 2 hJ, ?_⟩
      rw [coeff_reducePolynomial, h0, Int.cast_one]
    calc
      _ ≤ f2Probability (n - 1) (fun p ↦ reducePolynomial 2 J ∣ p) := by
        apply uniformProbability_mono
        intro w hw
        exact reducePolynomial_dvd 2 hw
      _ ≤ _ := f2Probability_divisible_le hn hred
  · rw [binaryProbability_divisible_eq_zero_of_constant _ hJ h0]
    positivity

end OdlyzkoPoonen
