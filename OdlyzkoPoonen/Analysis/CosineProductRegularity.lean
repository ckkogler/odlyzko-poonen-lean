import OdlyzkoPoonen.Analysis.CosineProductExpansion

/-!
# Regularity of cosine products and their quadratic forms
-/

namespace OdlyzkoPoonen
open scoped BigOperators

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

lemma cosineSquareProduct_continuous (L : ι → V →L[ℝ] ℝ) :
    Continuous (cosineSquareProduct L) := by
  unfold cosineSquareProduct
  fun_prop

lemma cosineSquareProduct_analyticAt (L : ι → V →L[ℝ] ℝ) (x : V) :
    AnalyticAt ℝ (cosineSquareProduct L) x := by
  unfold cosineSquareProduct
  apply Finset.analyticAt_fun_prod
  intro i _
  exact (Real.analyticAt_cos.comp ((L i).analyticAt x)).pow 2

lemma cosineQuadraticForm_continuous (L : ι → V →L[ℝ] ℝ) :
    Continuous (cosineQuadraticForm L) := by
  unfold cosineQuadraticForm
  fun_prop

lemma cosineQuadraticForm_analyticAt (L : ι → V →L[ℝ] ℝ) (x : V) :
    AnalyticAt ℝ (cosineQuadraticForm L) x := by
  unfold cosineQuadraticForm
  apply Finset.analyticAt_fun_sum
  intro i _
  exact ((L i).analyticAt x).pow 2

lemma cosineSquareProduct_nonneg (L : ι → V →L[ℝ] ℝ) (x : V) :
    0 ≤ cosineSquareProduct L x := Finset.prod_nonneg (fun _ _ ↦ sq_nonneg _)

lemma cosineSquareProduct_zero (L : ι → V →L[ℝ] ℝ) : cosineSquareProduct L 0 = 1 := by
  simp [cosineSquareProduct]

lemma cosineQuadraticForm_homogeneous (L : ι → V →L[ℝ] ℝ) (t : ℝ) (x : V) :
    cosineQuadraticForm L (t • x) = t ^ 2 * cosineQuadraticForm L x := by
  simp only [cosineQuadraticForm, map_smul, smul_eq_mul, mul_pow, Finset.mul_sum]

end OdlyzkoPoonen
