import OdlyzkoPoonen.Asymptotics.MonicDivisorLeadingTerm
import OdlyzkoPoonen.Analysis.LatticeGaussianVolume

/-!
# Determinant leading constant for periodic monic divisibility

The canonical monic remainder coordinates give a finite Gram determinant.
The full-degree asymptotic has an explicit coefficient and an error improved
by one full inverse power, uniformly across all residue classes.
-/

namespace OdlyzkoPoonen
noncomputable section
open Polynomial MeasureTheory Filter Asymptotics Matrix
open scoped BigOperators Classical

/-- The Gram matrix of one period of the canonical monic remainder coordinates. -/
def monicDivisorGramMatrix (f : ℤ[X]) (q : ℕ) :
    Matrix (Fin f.natDegree) (Fin f.natDegree) ℝ :=
  latticeGramMatrix (fun i : Fin q ↦ powerRemainderCoordinates f i.val)

lemma monicDivisorGaussianVolume_eq {f : ℤ[X]} (hf : f.Monic)
    {q : ℕ} (hq : 0 < q) (hperiod : f ∣ X ^ q - 1) :
    monicDivisorGaussianVolume f q =
      Real.pi ^ (-(f.natDegree : ℝ) / 2) / Real.sqrt (monicDivisorGramMatrix f q).det := by
  have hdegree : f.natDegree ≤ q := by
    have hn : (X ^ q - 1 : ℤ[X]) ≠ 0 := by
      simpa only [C_1] using X_pow_sub_C_ne_zero (R := ℤ) hq 1
    simpa only [← C_1, natDegree_X_pow_sub_C] using natDegree_le_of_dvd hperiod hn
  let e : Fin f.natDegree ↪ Fin q := ⟨fun i ↦ ⟨i.val, i.isLt.trans_le hdegree⟩,
    fun i j h ↦ Fin.ext (congrArg (fun z : Fin q ↦ z.val) h)⟩
  have he := lattice_gaussian_volume (fun i : Fin q ↦ powerRemainderCoordinates f i.val) e
    (by
      intro i
      ext j
      change powerRemainderCoordinates f i.val j = _
      rw [powerRemainderCoordinates_basis hf]
      by_cases hj : j = i <;> simp [hj])
  simpa only [Fintype.card_fin, monicDivisorGaussianVolume, monicDivisorGramMatrix] using! he

/-- Exact Gaussian determinant coefficient in terms of the full polynomial degree. -/
theorem degreeProbability_monic_determinant_leading_term {f : ℤ[X]} (hf : f.Monic)
    {q : ℕ} (hq : 0 < q) (hperiod : f ∣ X ^ q - 1)
    (hgeom : f ∣ ∑ j ∈ Finset.range q, (X : ℤ[X]) ^ j) :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ f ∣ p) -
      (((2 * q : ℕ) : ℝ) / Real.pi) ^ ((f.natDegree : ℝ) / 2) /
        Real.sqrt (monicDivisorGramMatrix f q).det * (n : ℝ) ^ (-(f.natDegree : ℝ) / 2))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-(f.natDegree : ℝ) / 2 - 1)) := by
  have he := degreeProbability_monic_gaussian_leading_term hf hq hperiod hgeom
  rw [monicDivisorGaussianVolume_eq hf hq hperiod] at he
  have hpow : -((f.natDegree : ℝ) / 2) = -(f.natDegree : ℝ) / 2 := by ring
  simp only [Real.div_rpow (Nat.cast_nonneg (2 * q)) Real.pi_nonneg,
    ← hpow, Real.rpow_neg Real.pi_nonneg] at he ⊢
  convert! he using 1
  funext n
  ring

end
end OdlyzkoPoonen
