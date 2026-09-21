import OdlyzkoPoonen.Analysis.GaussianDeterminant
import OdlyzkoPoonen.Analysis.LatticeCosineGaussianBound

/-!
# Exact Gaussian volumes for full-rank integer periods

The integer period vectors determine a finite Gram matrix. Containment of the
standard basis proves positive definiteness, so its determinant evaluates the
Gaussian volume exactly.
-/

namespace OdlyzkoPoonen
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Classical

variable {d ι : Type*} [Fintype d] [Fintype ι] [DecidableEq d]

def latticeCoordinateMatrix (v : ι → d → ℤ) : Matrix ι d ℝ := fun i j ↦ (v i j : ℝ)

def latticeGramMatrix (v : ι → d → ℤ) : Matrix d d ℝ :=
  (latticeCoordinateMatrix v)ᵀ * latticeCoordinateMatrix v

omit [DecidableEq d] in
lemma latticeGramMatrix_quadratic (v : ι → d → ℤ) (x : d → ℝ) :
    x ⬝ᵥ (latticeGramMatrix v *ᵥ x) =
      ∑ i, (integerLinearForm (v i) (WithLp.toLp 2 x)) ^ 2 := by
  rw [latticeGramMatrix, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, mulVec, latticeCoordinateMatrix, integerLinearForm_apply,
    pow_two]

lemma latticeGramMatrix_posDef (v : ι → d → ℤ) (e : d ↪ ι)
    (hbasis : ∀ i, v (e i) = Pi.single i 1) : (latticeGramMatrix v).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · simpa only [latticeGramMatrix, conjTranspose_eq_transpose_of_trivial] using
      isHermitian_conjTranspose_mul_self (latticeCoordinateMatrix v)
  · intro x hx
    have hAx : latticeCoordinateMatrix v *ᵥ x ≠ 0 := by
      intro he
      apply hx
      ext j
      have hj := congrFun he (e j)
      simpa [mulVec, dotProduct, latticeCoordinateMatrix, hbasis, Pi.single_apply] using hj
    have hp := (dotProduct_star_self_pos_iff (v := latticeCoordinateMatrix v *ᵥ x)).mpr hAx
    simpa only [star_trivial, latticeGramMatrix, ← mulVec_mulVec,
      dotProduct_mulVec, vecMul_transpose] using hp

omit [DecidableEq d] in
lemma lattice_cosine_quadratic_eq_gram (v : ι → d → ℤ) (x : EuclideanSpace ℝ d) :
    cosineQuadraticForm (fun i ↦ Real.pi • integerLinearForm (v i)) x =
      Real.pi ^ 2 * (x.ofLp ⬝ᵥ (latticeGramMatrix v *ᵥ x.ofLp)) := by
  rw [latticeGramMatrix_quadratic]
  simp only [cosineQuadraticForm, _root_.smul_apply, smul_eq_mul, mul_pow,
    WithLp.toLp_ofLp, Finset.mul_sum]

/-- Exact determinant evaluation of the lattice quadratic Gaussian. -/
theorem lattice_gaussian_volume (v : ι → d → ℤ) (e : d ↪ ι)
    (hbasis : ∀ i, v (e i) = Pi.single i 1) :
    (∫ x : EuclideanSpace ℝ d,
      Real.exp (-cosineQuadraticForm (fun i ↦ Real.pi • integerLinearForm (v i)) x)) =
      Real.pi ^ (-(Fintype.card d : ℝ) / 2) / Real.sqrt (latticeGramMatrix v).det := by
  simp only [lattice_cosine_quadratic_eq_gram, ← neg_mul]
  rw [integral_gaussian_posDef (latticeGramMatrix v) (latticeGramMatrix_posDef v e hbasis)
    (sq_pos_of_pos Real.pi_pos)]
  have hpi : Real.pi / Real.pi ^ 2 = Real.pi⁻¹ := by field_simp
  rw [hpi, Real.inv_rpow Real.pi_nonneg, ← Real.rpow_neg Real.pi_nonneg]
  congr 2
  ring

end
end OdlyzkoPoonen
