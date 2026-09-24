import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Gaussian bounds for products of squared cosines

On a fundamental interval, a squared cosine is bounded by a Gaussian.
Selecting factors along independent coordinate directions gives a global
Gaussian bound on the whole fundamental cube, with no compactness argument.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma cosine_half_sq_le_gaussian {x : ℝ} (hx : |x| ≤ Real.pi) :
    Real.cos (x / 2) ^ 2 ≤ Real.exp (-(x ^ 2 / Real.pi ^ 2)) := by
  have hc := Real.cos_le_one_sub_mul_cos_sq hx
  have hdouble := Real.cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hdouble
  have he := Real.add_one_le_exp (-(x ^ 2 / Real.pi ^ 2))
  have hs : Real.cos (x / 2) ^ 2 ≤ 1 - x ^ 2 / Real.pi ^ 2 := by
    have hc' : Real.cos x ≤ 1 - 2 * (x ^ 2 / Real.pi ^ 2) := by
      convert hc using 1; ring
    nlinarith
  linarith

lemma prod_cosine_half_sq_le_gaussian {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∀ i, |x i| ≤ Real.pi) :
    (∏ i, Real.cos (x i / 2) ^ 2) ≤
      Real.exp (-(∑ i, x i ^ 2) / Real.pi ^ 2) := by
  calc
    _ ≤ ∏ i, Real.exp (-(x i ^ 2 / Real.pi ^ 2)) :=
      Finset.prod_le_prod₀ (fun _ _ ↦ sq_nonneg _) (fun i _ ↦ cosine_half_sq_le_gaussian (hx i))
    _ = _ := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, neg_div]

/-- Extra cosine-square factors can only improve the selected-coordinate bound. -/
theorem prod_cosine_half_sq_le_selected_gaussian {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ↪ ι) (x : ι → ℝ) (hx : ∀ i, |x (e i)| ≤ Real.pi) :
    (∏ j, Real.cos (x j / 2) ^ 2) ≤
      Real.exp (-(∑ i, x (e i) ^ 2) / Real.pi ^ 2) := by
  classical
  calc
    _ ≤ ∏ j ∈ Finset.univ.image e, Real.cos (x j / 2) ^ 2 := by
      apply Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.subset_univ _)
      · intro j _
        exact sq_nonneg _
      · intro j _ _
        exact Real.cos_sq_le_one _
    _ = ∏ i, Real.cos (x (e i) / 2) ^ 2 := by
      rw [Finset.prod_image]
      exact fun _ _ _ _ h ↦ e.injective h
    _ ≤ _ := prod_cosine_half_sq_le_gaussian (x ∘ e) hx

end OdlyzkoPoonen
