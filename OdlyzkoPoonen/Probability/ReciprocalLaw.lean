import OdlyzkoPoonen.FiniteField.ReciprocalPairs
import OdlyzkoPoonen.Probability.PrescribedBits
import OdlyzkoPoonen.Probability.AverageBounds

/-!
# Exact probability and count of reciprocal endpoint polynomials

In the opposite-pair coordinates, reciprocity prescribes every pair-sum bit
to be zero. The free lower and central coefficients impose no constraints.
This proves the exact law, and hence the exact count, directly in the existing
uniform model. Here `n` counts internal coefficients, so the degree is `n + 1`.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical

lemma f2Probability_reciprocal (n : ℕ) :
    f2Probability n (fun p ↦ p.reverse = p) = (1 / 2 : ℝ) ^ (n / 2) := by
  classical
  rw [f2Probability_eq_paired_average]
  simp_rw [pairedPolynomial_reverse_eq_iff, uniformProbability_eq_average_indicator,
    uniformAverage_const]
  rw [← uniformProbability_eq_average_indicator]
  simpa only [Finset.mem_univ, forall_true_left, Finset.card_univ,
    Fintype.card_fin] using
    (uniformProbability_prescribedBits (Finset.univ : Finset (Fin (n / 2)))
      (fun _ ↦ false))

lemma card_reciprocal_f2Family (n : ℕ) :
    ((f2Family n).filter (fun p ↦ p.reverse = p)).card = 2 ^ ((n + 1) / 2) := by
  classical
  letI : DecidablePred (fun p : (ZMod 2)[X] ↦ p.reverse = p) :=
    fun _ ↦ Classical.propDecidable _
  have h := f2Probability_reciprocal n
  rw [f2Probability_eq_count, one_div_pow] at h
  have hpow : (2 : ℝ) ^ n = 2 ^ ((n + 1) / 2) * 2 ^ (n / 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hc : (((f2Family n).filter (fun p ↦ p.reverse = p)).card : ℝ) =
      (2 : ℝ) ^ ((n + 1) / 2) := by
    have heq := (div_eq_iff (show (2 : ℝ) ^ n ≠ 0 by positivity)).mp h
    rw [hpow] at heq
    field_simp at heq
    exact heq
  norm_cast at hc
  convert hc using 1
  congr 1
  ext p
  simp only [Finset.mem_filter]

end OdlyzkoPoonen
