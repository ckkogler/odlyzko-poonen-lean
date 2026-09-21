import OdlyzkoPoonen.Analysis.IntegerFourierCharacters
import OdlyzkoPoonen.Analysis.CosineSquareBound

/-!
# Global Gaussian domination from lattice basis vectors

When the period vectors include the standard integer basis, the cosine
product has a Gaussian bound throughout the centered unit cube. The same
selected coordinates make its quadratic form uniformly positive definite.
-/

namespace OdlyzkoPoonen
open scoped BigOperators Classical

variable {d ι : Type*} [Fintype d] [Fintype ι]

lemma integerLinearForm_standard_basis (i : d) (x : EuclideanSpace ℝ d) :
    integerLinearForm (Pi.single i 1) x = x i := by
  simp [integerLinearForm_apply, Pi.single_apply]

theorem lattice_cosine_quadratic_coercive (v : ι → d → ℤ) (e : d ↪ ι)
    (hbasis : ∀ i, v (e i) = Pi.single i 1) (x : EuclideanSpace ℝ d) :
    4 * ‖x‖ ^ 2 ≤ cosineQuadraticForm (fun i ↦ Real.pi • integerLinearForm (v i)) x := by
  have hs : ∑ j : d, (Real.pi * x j) ^ 2 ≤ ∑ i : ι, (Real.pi * integerLinearForm (v i) x) ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.univ.image e, (Real.pi * integerLinearForm (v i) x) ^ 2 := by
        rw [Finset.sum_image (fun _ _ _ _ h ↦ e.injective h)]
        simp only [hbasis, integerLinearForm_standard_basis]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ ↦ sq_nonneg _)
  have he : (∑ j : d, (Real.pi * x j) ^ 2) = Real.pi ^ 2 * ‖x‖ ^ 2 := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]
  rw [he] at hs
  have hpi : 4 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hh := mul_le_mul_of_nonneg_right hpi (sq_nonneg ‖x‖)
  exact hh.trans hs

theorem lattice_cosine_product_gaussian_bound (v : ι → d → ℤ) (e : d ↪ ι)
    (hbasis : ∀ i, v (e i) = Pi.single i 1) (x : EuclideanSpace ℝ d)
    (hx : ∀ j, |x j| ≤ (1 / 2 : ℝ)) :
    cosineSquareProduct (fun i ↦ Real.pi • integerLinearForm (v i)) x ≤
      Real.exp (-4 * ‖x‖ ^ 2) := by
  have hsel (j : d) : |2 * Real.pi * integerLinearForm (v (e j)) x| ≤ Real.pi := by
    rw [hbasis, integerLinearForm_standard_basis, abs_mul,
      abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)]
    nlinarith [hx j, Real.pi_pos]
  have he := prod_cosine_half_sq_le_selected_gaussian e
    (fun i ↦ 2 * Real.pi * integerLinearForm (v i) x) hsel
  have hhalf (i : ι) : (2 * Real.pi * integerLinearForm (v i) x) / 2 =
      Real.pi * integerLinearForm (v i) x := by ring
  simp only [hhalf, hbasis, integerLinearForm_standard_basis] at he
  have hexp : -(∑ j : d, (2 * Real.pi * x j) ^ 2) / Real.pi ^ 2 = -4 * ‖x‖ ^ 2 := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]
    field_simp
    ring
  rw [hexp] at he
  exact he

end OdlyzkoPoonen
