import OdlyzkoPoonen.ModFour.FiberEstimate
import OdlyzkoPoonen.FiniteField.FirstAsymmetry
import OdlyzkoPoonen.FiniteField.Convolution
import OdlyzkoPoonen.FiniteField.PairSumPrefix
import OdlyzkoPoonen.Probability.LeadingFalseBits

/-!
# The exact average of the actual toggle slopes

If the first asymmetry of `a` is at `j`, factor `a+a.reverse` by `X^j`. The
remaining factor has constant one. The first `j` slopes vanish and the remaining
slopes are convolution of the first `m-j` pair-sum bits by that factor. Proved
prefix uniformity and triangular convolution therefore give the exact average
`(3/4)^(m-j)` for the active-index weight in the polynomial fiber estimate.
-/

namespace OdlyzkoPoonen
open Polynomial

/-- The actual toggle-slope coefficients, indexed from the first positive coefficient. -/
noncomputable def exposureSlopeWord {n : ℕ} (a : (ZMod 2)[X])
    (c : Fin (n / 2) → Bool) (i : Fin (n / 2)) : Bool :=
  f2ToBit (((a + a.reverse) * pairSumPolynomial c).coeff (i.val + 1))

lemma activeDiscrepancyIndices_card {n : ℕ} (a : (ZMod 2)[X]) (c : Fin (n / 2) → Bool) :
    (activeDiscrepancyIndices a c).card = trueBitCount (exposureSlopeWord a c) := by
  simp only [activeDiscrepancyIndices, trueBitCount, exposureSlopeWord, f2ToBit_eq_true_iff]

lemma exposureSlopeWord_zero_before {n j : ℕ} {a : (ZMod 2)[X]}
    (ha : FirstAsymmetryAt a j) (c : Fin (n / 2) → Bool) {i : Fin (n / 2)}
    (hi : i.val + 1 ≤ j) : exposureSlopeWord a c i = false := by
  apply (f2ToBit_eq_false_iff _).mpr
  exact coeff_mul_zero_through_initial ha.2 (coeff_pairSumPolynomial_zero c) hi

lemma exposureSlopeWord_shifted {n j : ℕ} {a q : (ZMod 2)[X]}
    (hj : j ≤ n / 2) (hfactor : a + a.reverse = X ^ j * q)
    (c : Fin (n / 2) → Bool) (i : Fin (n / 2 - j)) :
    exposureSlopeWord a c (shiftedWordIndex hj i) =
      coefficientConvolution q (wordPrefix (Nat.sub_le (n / 2) j) c) i := by
  apply congrArg f2ToBit
  change ((a + a.reverse) * pairSumPolynomial c).coeff (j + i.val + 1) =
    (q * f2InteriorPolynomial (wordPrefix (Nat.sub_le (n / 2) j) c)).coeff (i.val + 1)
  rw [Nat.add_assoc, coeff_mul_after_X_pow_factor _ hfactor]
  apply coeff_mul_right_eq_of_prefix
  intro k hk
  apply pairSumPolynomial_prefix
  have := i.isLt
  omega

lemma uniformAverage_active_discrepancy_weight {n j : ℕ} {a : (ZMod 2)[X]}
    (ha : FirstAsymmetryAt a j) (hj : j ≤ n / 2) :
    uniformAverage (fun c : Fin (n / 2) → Bool ↦
      (1 / 2 : ℝ) ^ (activeDiscrepancyIndices a c).card) = (3 / 4 : ℝ) ^ (n / 2 - j) := by
  obtain ⟨q, hfactor, hq⟩ := exists_X_pow_factor_of_initial_one ha.2 ha.1
  have hcount (c : Fin (n / 2) → Bool) :
      (activeDiscrepancyIndices a c).card =
        trueBitCount (coefficientConvolution q (wordPrefix (Nat.sub_le (n / 2) j) c)) := by
    rw [activeDiscrepancyIndices_card, trueBitCount_eq_shifted hj _
      (fun i hi ↦ exposureSlopeWord_zero_before ha c (by omega))]
    congr 1
    funext i
    exact exposureSlopeWord_shifted hj hfactor c i
  simp only [hcount]
  exact (uniformAverage_wordPrefix (Nat.sub_le (n / 2) j)
    (fun w : Fin (n / 2 - j) → Bool ↦ (1 / 2 : ℝ) ^ trueBitCount (coefficientConvolution q w))).trans
    (uniformAverage_coefficientConvolution_half_weight hq)

/-- The fixed-first-factor bound following the exact slope average. -/
lemma f2_factor_congruence_probability_le_of_firstAsymmetry {d n j : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (hfirst : FirstAsymmetryAt a j) (hj : j ≤ n / 2) :
    f2Probability n (fun b ↦
      CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
        (autocorrelation (zeroOneLift (a * b.reverse)))) ≤ (3 / 4 : ℝ) ^ (n / 2 - j) :=
  (f2_factor_congruence_probability_le_average ha).trans_eq
    (uniformAverage_active_discrepancy_weight hfirst hj)

end OdlyzkoPoonen
