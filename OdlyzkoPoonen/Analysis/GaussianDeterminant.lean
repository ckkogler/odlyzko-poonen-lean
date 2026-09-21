import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Gaussian integrals and positive definite determinants

A positive definite matrix factors as a transpose times itself. Linear change
of variables reduces its Gaussian integral to the ordinary radial Gaussian,
with the determinant supplying the exact volume factor.
-/

namespace OdlyzkoPoonen
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators MatrixOrder

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma integral_gaussian_linearMap (L : V →ₗ[ℝ] V) (hL : LinearMap.det L ≠ 0)
    {b : ℝ} (hb : 0 < b) :
    (∫ x : V, Real.exp (-b * ‖L x‖ ^ 2)) =
      |(LinearMap.det L)⁻¹| * (Real.pi / b) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  have hc : Continuous (fun y : V ↦ Real.exp (-b * ‖y‖ ^ 2)) := by fun_prop
  have he := integral_map_of_stronglyMeasurable
    L.continuous_of_finiteDimensional.measurable hc.stronglyMeasurable (μ := volume)
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hL, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul,
    GaussianFourier.integral_rexp_neg_mul_sq_norm hb] at he
  exact he.symm

variable {d : Type*} [Fintype d] [DecidableEq d]

lemma matrix_gram_quadratic_eq_norm_sq (B : Matrix d d ℝ) (x : EuclideanSpace ℝ d) :
    x.ofLp ⬝ᵥ ((Bᵀ * B) *ᵥ x.ofLp) = ‖B.toEuclideanLin x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp, star_trivial]
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- The determinant formula, with the usual unnormalized Euclidean volume. -/
theorem integral_gaussian_posDef (G : Matrix d d ℝ) (hG : G.PosDef)
    {b : ℝ} (hb : 0 < b) :
    (∫ x : EuclideanSpace ℝ d, Real.exp (-b * (x.ofLp ⬝ᵥ (G *ᵥ x.ofLp)))) =
      (Real.pi / b) ^ ((Fintype.card d : ℝ) / 2) / Real.sqrt G.det := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.posSemidef.nonneg
  have hB' : G = Bᵀ * B := by simpa only [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hB
  have hdet : B.det ^ 2 = G.det := by rw [hB', det_mul, det_transpose]; ring
  have hBd : B.det ≠ 0 := by
    intro he
    have hp := hG.det_pos
    rw [he, zero_pow (by omega : 2 ≠ 0)] at hdet
    linarith
  have hroot : Real.sqrt G.det = |B.det| := by rw [← hdet, Real.sqrt_sq_eq_abs]
  have hLd : LinearMap.det B.toEuclideanLin = B.det := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
  have he := integral_gaussian_linearMap B.toEuclideanLin (by rwa [hLd]) hb
  simp only [hLd, finrank_euclideanSpace] at he
  rw [hB']
  simp_rw [matrix_gram_quadratic_eq_norm_sq]
  rw [he, ← hB', hroot, abs_inv]
  ring

end
end OdlyzkoPoonen
