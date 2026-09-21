import OdlyzkoPoonen.Analysis.BinomialHalfPowerPolynomial
import OdlyzkoPoonen.Analysis.PoweredGaussianAmplitudes

/-!
# A fixed polynomial for the Gaussian moment expansion

Vanishing of low homogeneous coefficients removes all potentially negative
powers. The finite moment formula is consequently an ordinary polynomial
evaluated at the inverse square root of the large integer.
-/

namespace OdlyzkoPoonen
open Polynomial MeasureTheory
open scoped BigOperators

noncomputable def gaussianMomentPolynomial (d R : ℕ) (c : ℕ → ℕ → ℝ) : ℝ[X] :=
  ∑ r ∈ Finset.range R, ∑ j ∈ Finset.range (4 * R),
    if 4 * r ≤ j then binomialHalfPowerPolynomial (d + j) r (c r j) else 0

lemma gaussianMomentPolynomial_coeff_zero (d R : ℕ) (hd : 0 < d) (c : ℕ → ℕ → ℝ) :
    (gaussianMomentPolynomial d R c).coeff 0 = 0 := by
  unfold gaussianMomentPolynomial
  simp only [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro j hj
  split_ifs with h
  · exact binomialHalfPowerPolynomial_coeff_zero _ _ (by omega) _
  · simp

theorem gaussianMomentPolynomial_eval (d R n : ℕ) (c : ℕ → ℕ → ℝ)
    (hn : 1 ≤ n) (hRn : R ≤ n)
    (hc : ∀ r < R, ∀ j < 4 * r, c r j = 0) :
    (gaussianMomentPolynomial d R c).eval ((Real.sqrt (n : ℝ))⁻¹) =
      ∑ r ∈ Finset.range R, (n.choose r : ℝ) *
        ∑ j ∈ Finset.range (4 * R), (n : ℝ) ^ (-((d : ℝ) + j) / 2) * c r j := by
  unfold gaussianMomentPolynomial
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjr : 4 * r ≤ j
  · rw [ite_eq_left hjr, binomialHalfPowerPolynomial_eval_inverse_sqrt n (d + j) r hn
      (by have := Finset.mem_range.mp hr; omega) (by omega)]
    push_cast
    ring
  · rw [ite_eq_right hjr, eval_zero, hc r (Finset.mem_range.mp hr) j (by omega)]
    ring

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma gaussianAmplitudeCoefficient_vanishing
    {ψ Q h : V → ℝ} [MeasureSpace V]
    (hQ : ContinuousAt Q 0) (hh : ContinuousAt h 0)
    (hδ : (fun x ↦ ψ x - Real.exp (-Q x)) =O[nhds 0] (fun x : V ↦ ‖x‖ ^ 4))
    (r : ℕ) {p : FormalMultilinearSeries ℝ V ℝ}
    (hp : HasFPowerSeriesAt (poweredGaussianAmplitude ψ Q h r) p 0)
    (j : ℕ) (hj : j < 4 * r) :
    (∫ x : V, p j (fun _ ↦ x) * Real.exp (-Q x)) = 0 := by
  have he (x : V) := poweredGaussianAmplitude_low_coefficient hQ hh hδ r hp j hj x
  simp only [he, zero_mul, integral_zero]

end OdlyzkoPoonen
