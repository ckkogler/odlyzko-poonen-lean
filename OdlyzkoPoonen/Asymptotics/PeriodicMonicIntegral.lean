import OdlyzkoPoonen.Probability.PeriodicBernoulliIntegral
import OdlyzkoPoonen.Analysis.LatticeCosineExpansion

/-!
# Periodic monic divisors and asymptotic block expansions

Canonical remainder coordinates identify divisibility with a full-lattice
Bernoulli sum. A zero-sum period yields fixed analytic amplitudes and an
arbitrary-order expansion on each fixed residual block.
-/

namespace OdlyzkoPoonen
noncomputable section
open Polynomial MeasureTheory Filter Asymptotics
open scoped BigOperators Classical

/-- The finite remaining bits and the two fixed endpoint coefficients. -/
def monicDivisorAmplitude (f : ℤ[X]) (r : ℕ) : EuclideanSpace ℝ (Fin f.natDegree) → ℝ :=
  finiteCharacterAmplitude (fun w : Fin r → Bool ↦
    powerRemainderCoordinates f 0 + powerRemainderCoordinates f (r + 1) +
      ∑ i, bitValue (w i) • powerRemainderCoordinates f (i.val + 1))

theorem binaryProbability_periodic_monic_integral {f : ℤ[X]} (hf : f.Monic)
    {q : ℕ} (hq : 0 < q) (hperiod : f ∣ X ^ q - 1)
    (hgeom : f ∣ ∑ j ∈ Finset.range q, (X : ℤ[X]) ^ j) (k r : ℕ) :
    binaryProbability (2 * q * k + r) (fun p ↦ f ∣ p) =
      ∫ x in unitFourierCube (Fin f.natDegree),
        monicDivisorAmplitude f r x *
          cosineSquareProduct (fun i : Fin q ↦
            Real.pi • integerLinearForm (powerRemainderCoordinates f i.val)) x ^ k := by
  have hv := powerRemainderCoordinates_periodic hf hperiod
  have hz : ∑ j : Fin q, powerRemainderCoordinates f j.val = 0 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact powerRemainderCoordinates_sum_eq_zero hf hgeom
  have hend : powerRemainderCoordinates f (2 * q * k + r + 1) =
      powerRemainderCoordinates f (r + 1) := by
    rw [show 2 * q * k + r + 1 = (r + 1) + q * (2 * k) by ring]
    exact periodic_nat_add_mul hv (r + 1) (2 * k)
  unfold binaryProbability
  have he : (fun w : Fin (2 * q * k + r) → Bool ↦ f ∣ wordPolynomial w) =
      (fun w : Fin (2 * q * k + r) → Bool ↦
        powerRemainderCoordinates f 0 + powerRemainderCoordinates f (r + 1) +
          ∑ i, bitValue (w i) • powerRemainderCoordinates f (i.val + 1) = 0) := by
    funext w
    apply propext
    rw [dvd_wordPolynomial_iff_remainderCoordinates_eq_zero hf, hend]
    simp only [add_assoc, add_comm, add_left_comm]
  rw [he]
  have hp := uniformProbability_periodic_bit_vector_zero
    (powerRemainderCoordinates f 0 + powerRemainderCoordinates f (r + 1))
    (powerRemainderCoordinates f) hq hv hz k r
  convert hp using 1
  apply setIntegral_congr_fun (unitFourierCube_measurable _)
  intro x _
  congr 1

/-- Each fixed residual block has fixed half-power coefficients to every order. -/
theorem binaryProbability_periodic_monic_block_expansion {f : ℤ[X]} (hf : f.Monic)
    (hd : 0 < f.natDegree) {q : ℕ} (hq : 0 < q) (hperiod : f ∣ X ^ q - 1)
    (hgeom : f ∣ ∑ j ∈ Finset.range q, (X : ℤ[X]) ^ j) (r R : ℕ) (hR : 1 ≤ R) :
    ∃ c : ℕ → ℝ, c 0 = 0 ∧
      (fun k : ℕ ↦ binaryProbability (2 * q * k + r) (fun p ↦ f ∣ p) -
        ∑ j ∈ Finset.range (2 * R), c j * (k : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop]
          (fun k : ℕ ↦ (k : ℝ) ^ (-(R : ℝ))) := by
  have hdegree : f.natDegree ≤ q := by
    have hn : (X ^ q - 1 : ℤ[X]) ≠ 0 := by
      simpa only [C_1] using X_pow_sub_C_ne_zero (R := ℤ) hq 1
    simpa only [← C_1, natDegree_X_pow_sub_C] using natDegree_le_of_dvd hperiod hn
  let e : Fin f.natDegree ↪ Fin q := ⟨fun i ↦ ⟨i.val, i.isLt.trans_le hdegree⟩,
    fun i j h ↦ Fin.ext (congrArg (fun z : Fin q ↦ z.val) h)⟩
  have he := lattice_cosine_integral_half_expansion
    (fun i : Fin q ↦ powerRemainderCoordinates f i.val) e
    (by
      intro i
      ext j
      change powerRemainderCoordinates f i.val j = _
      rw [powerRemainderCoordinates_basis hf]
      by_cases hj : j = i <;> simp [hj])
    (by simpa using hd) (h := monicDivisorAmplitude f r)
    (finiteCharacterAmplitude_continuous _) (finiteCharacterAmplitude_analyticAt _ 0) R hR
  simpa only [binaryProbability_periodic_monic_integral hf hq hperiod hgeom] using he

end
end OdlyzkoPoonen
