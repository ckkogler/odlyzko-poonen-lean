import OdlyzkoPoonen.Analysis.GaussianLeadingTerm
import OdlyzkoPoonen.Analysis.LatticeCosineExpansion

/-!
# Leading Gaussian term for lattice cosine integrals

The full lattice basis excludes additional maxima on the unit cube. The leading
coefficient is the Gaussian volume times the amplitude at zero, and the error
improves by one full inverse power.
-/

namespace OdlyzkoPoonen
open MeasureTheory Filter Asymptotics
open scoped BigOperators Topology Classical

variable {d ι : Type*} [Fintype d] [Fintype ι]

theorem lattice_cosine_integral_leading_term (v : ι → d → ℤ) (e : d ↪ ι)
    (hbasis : ∀ i, v (e i) = Pi.single i 1)
    {h : EuclideanSpace ℝ d → ℝ} (hh : Continuous h) (hha : AnalyticAt ℝ h 0) :
    (fun n : ℕ ↦ (∫ x in unitFourierCube d,
      h x * cosineSquareProduct (fun i ↦ Real.pi • integerLinearForm (v i)) x ^ n) -
      (n : ℝ) ^ (-(Fintype.card d : ℝ) / 2) * h 0 *
        ∫ x : EuclideanSpace ℝ d,
          Real.exp (-cosineQuadraticForm (fun i ↦ Real.pi • integerLinearForm (v i)) x))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-(Fintype.card d : ℝ) / 2 - 1)) := by
  let A : ι → EuclideanSpace ℝ d →L[ℝ] ℝ := fun i ↦ Real.pi • integerLinearForm (v i)
  let ψ := cosineSquareProduct A
  let Q := cosineQuadraticForm A
  have hψc : Continuous ψ := cosineSquareProduct_continuous A
  have hQc : Continuous Q := cosineQuadraticForm_continuous A
  have hδc : Continuous (fun x ↦ ψ x - Real.exp (-Q x)) := by fun_prop
  have hδo : (fun x ↦ ψ x - Real.exp (-Q x)) =O[𝓝 0] (fun x ↦ ‖x‖ ^ 4) :=
    cosineSquareProduct_gaussian_isBigO A
  obtain ⟨C, hC, hδ⟩ := compact_power_bound_of_local (closedUnitFourierCube_compact d)
    hδc.continuousOn 4 hδo
  obtain ⟨H, hH⟩ := (closedUnitFourierCube_compact d).exists_bound_of_continuousOn hh.continuousOn
  have hhv : ∀ x ∈ unitFourierCube d, |h x| ≤ |H| := by
    intro x hx
    have he := hH x (unitFourierCube_subset_closed d hx)
    exact (show |h x| ≤ H from he).trans (le_abs_self H)
  have he := analytic_power_integral_leading_term (unitFourierCube_measurable d)
    (closedUnitFourierCube_compact d) (unitFourierCube_subset_closed d)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 4) hC.le (abs_nonneg H)
    (ball_subset_unitFourierCube d) hψc.continuousOn hQc hh.continuousOn hha
    (lattice_cosine_quadratic_coercive v e hbasis)
    (fun t _ x ↦ cosineQuadraticForm_homogeneous A t x)
    (fun x ↦ by simp [Q, cosineQuadraticForm, sq])
    (fun x _ ↦ cosineSquareProduct_nonneg A x)
    (fun x hx ↦ lattice_cosine_product_gaussian_bound v e hbasis x
      (abs_coordinate_le_half d (unitFourierCube_subset_closed d hx)))
    (fun x hx ↦ hδ x (unitFourierCube_subset_closed d hx)) hhv
  simpa only [finrank_euclideanSpace] using he

end OdlyzkoPoonen
