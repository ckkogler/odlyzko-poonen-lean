import OdlyzkoPoonen.Analysis.AnalyticPowerHalfExpansion
import OdlyzkoPoonen.Analysis.CosineProductRegularity
import OdlyzkoPoonen.Analysis.LatticeCosineGaussianBound
import OdlyzkoPoonen.Analysis.UnitFourierCube

/-!
# Arbitrary-order expansions for lattice cosine integrals

Standard basis vectors ensure Gaussian domination on the unit cube. The
analytic power theorem then gives fixed half-power coefficients to any
prescribed order, for every fixed analytic residual amplitude.
-/

namespace OdlyzkoPoonen
open MeasureTheory Filter Asymptotics
open scoped BigOperators Topology Classical

variable {d ι : Type*} [Fintype d] [Fintype ι]

theorem lattice_cosine_integral_half_expansion (v : ι → d → ℤ) (e : d ↪ ι)
    (hbasis : ∀ i, v (e i) = Pi.single i 1) (hd : 0 < Fintype.card d)
    {h : EuclideanSpace ℝ d → ℝ} (hh : Continuous h) (hha : AnalyticAt ℝ h 0)
    (R : ℕ) (hR : 1 ≤ R) :
    ∃ c : ℕ → ℝ, c 0 = 0 ∧
      (fun n : ℕ ↦ (∫ x in unitFourierCube d,
        h x * cosineSquareProduct (fun i ↦ Real.pi • integerLinearForm (v i)) x ^ n) -
        ∑ j ∈ Finset.range (2 * R), c j * (n : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop]
          (fun n : ℕ ↦ (n : ℝ) ^ (-(R : ℝ))) := by
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
  have hdim : 0 < Module.finrank ℝ (EuclideanSpace ℝ d) := by simpa using hd
  exact analytic_power_half_expansion (unitFourierCube_measurable d)
    (closedUnitFourierCube_compact d) (unitFourierCube_subset_closed d)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 4) hC.le (abs_nonneg H)
    (ball_subset_unitFourierCube d) hψc.continuousOn hQc hh.continuousOn
    (cosineSquareProduct_analyticAt A 0) (cosineQuadraticForm_analyticAt A 0) hha
    (lattice_cosine_quadratic_coercive v e hbasis)
    (fun t _ x ↦ cosineQuadraticForm_homogeneous A t x)
    (fun x _ ↦ cosineSquareProduct_nonneg A x)
    (fun x hx ↦ lattice_cosine_product_gaussian_bound v e hbasis x
      (abs_coordinate_le_half d (unitFourierCube_subset_closed d hx)))
    (fun x hx ↦ hδ x (unitFourierCube_subset_closed d hx)) hδo hhv hdim R hR

end OdlyzkoPoonen
