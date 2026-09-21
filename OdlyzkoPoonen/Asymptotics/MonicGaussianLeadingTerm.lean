import OdlyzkoPoonen.Asymptotics.PeriodicMonicIntegral
import OdlyzkoPoonen.Analysis.LatticeGaussianLeadingTerm

/-!
# Leading block-count asymptotic for periodic monic divisors

The endpoint and residual-bit amplitude is one at the origin. Consequently the
leading coefficient is the same Gaussian volume on every fixed residual block.
-/

namespace OdlyzkoPoonen
noncomputable section
open Polynomial MeasureTheory Filter Asymptotics
open scoped BigOperators Classical

/-- The quadratic Gaussian volume of one complete coordinate period. -/
def monicDivisorGaussianVolume (f : ℤ[X]) (q : ℕ) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin f.natDegree),
    Real.exp (-cosineQuadraticForm (fun i : Fin q ↦
      Real.pi • integerLinearForm (powerRemainderCoordinates f i.val)) x)

lemma monicDivisorAmplitude_zero (f : ℤ[X]) (r : ℕ) : monicDivisorAmplitude f r 0 = 1 :=
  finiteCharacterAmplitude_zero _

theorem binaryProbability_periodic_monic_block_leading_term {f : ℤ[X]} (hf : f.Monic)
    {q : ℕ} (hq : 0 < q) (hperiod : f ∣ X ^ q - 1)
    (hgeom : f ∣ ∑ j ∈ Finset.range q, (X : ℤ[X]) ^ j) (r : ℕ) :
    (fun k : ℕ ↦ binaryProbability (2 * q * k + r) (fun p ↦ f ∣ p) -
      (k : ℝ) ^ (-(f.natDegree : ℝ) / 2) * monicDivisorGaussianVolume f q)
      =O[atTop] (fun k : ℕ ↦ (k : ℝ) ^ (-(f.natDegree : ℝ) / 2 - 1)) := by
  have hdegree : f.natDegree ≤ q := by
    have hn : (X ^ q - 1 : ℤ[X]) ≠ 0 := by
      simpa only [C_1] using X_pow_sub_C_ne_zero (R := ℤ) hq 1
    simpa only [← C_1, natDegree_X_pow_sub_C] using natDegree_le_of_dvd hperiod hn
  let e : Fin f.natDegree ↪ Fin q := ⟨fun i ↦ ⟨i.val, i.isLt.trans_le hdegree⟩,
    fun i j h ↦ Fin.ext (congrArg (fun z : Fin q ↦ z.val) h)⟩
  have he := lattice_cosine_integral_leading_term
    (fun i : Fin q ↦ powerRemainderCoordinates f i.val) e
    (by
      intro i
      ext j
      change powerRemainderCoordinates f i.val j = _
      rw [powerRemainderCoordinates_basis hf]
      by_cases hj : j = i <;> simp [hj])
    (h := monicDivisorAmplitude f r)
    (finiteCharacterAmplitude_continuous _) (finiteCharacterAmplitude_analyticAt _ 0)
  simpa only [binaryProbability_periodic_monic_integral hf hq hperiod hgeom,
    monicDivisorAmplitude_zero, mul_one, Fintype.card_fin, monicDivisorGaussianVolume] using he

end
end OdlyzkoPoonen
