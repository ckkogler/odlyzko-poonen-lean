import OdlyzkoPoonen.Analysis.GaussianIntegralAsymptotics
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Gaussian integrals with analytic amplitudes

Each homogeneous Taylor coefficient contributes its Gaussian moment times
the corresponding half-integer power. The remainder is uniform on any
bounded measurable integration region containing a neighborhood of zero.
-/

namespace OdlyzkoPoonen
open MeasureTheory Filter Asymptotics
open scoped Topology BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The coefficient attached to one homogeneous Taylor term. -/
noncomputable def gaussianAmplitudeCoefficient (p : FormalMultilinearSeries ℝ V ℝ)
    (Q : V → ℝ) (j : ℕ) : ℝ :=
  ∫ x : V, p j (fun _ ↦ x) * Real.exp (-Q x)

/-- Arbitrary finite-order expansion of a Gaussian integral with analytic amplitude. -/
theorem analytic_gaussian_amplitude_expansion {K L : Set V}
    (hK : MeasurableSet K) (hL : IsCompact L) (hKL : K ⊆ L)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) (hball : Metric.ball 0 ε ⊆ K)
    {h Q : V → ℝ} {p : FormalMultilinearSeries ℝ V ℝ}
    (hh : ContinuousOn h L) (hp : HasFPowerSeriesAt h p 0)
    (hQc : Continuous Q) (hQb : ∀ x, b * ‖x‖ ^ 2 ≤ Q x)
    (hQs : ∀ (t : ℝ), 0 < t → ∀ x, Q (t • x) = t ^ 2 * Q x) (N : ℕ) :
    (fun n : ℕ ↦ (∫ x in K, h x * Real.exp (-(n : ℝ) * Q x)) -
      ∑ j ∈ Finset.range N, (n : ℝ) ^ (-((Module.finrank ℝ V : ℝ) + j) / 2) *
        gaussianAmplitudeCoefficient p Q j) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-((Module.finrank ℝ V : ℝ) + N) / 2)) := by
  obtain ⟨C, hC, hbound⟩ := analytic_partialSum_compact_remainder hL hh hp N
  have hrem := gaussian_weighted_remainder_isBigO hK N hC.le hb
    (h := fun x ↦ h x - p.partialSum N x) (Q := Q)
    (fun x hx ↦ hbound x (hKL hx)) (fun x _ ↦ hQb x)
  have htail (j : ℕ) (hj : j ∈ Finset.range N) :
      (fun n : ℕ ↦ ∫ x in Kᶜ, p j (fun _ ↦ x) * Real.exp (-(n : ℝ) * Q x)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-((Module.finrank ℝ V : ℝ) + N) / 2)) :=
    gaussian_tail_isBigO hK hε hb (norm_nonneg _) j N
      (Finset.mem_range.mp hj).le hball (multilinear_diagonal_bound (p j)) hQb
  have hsum := Asymptotics.IsBigO.sum htail
  have herror := hrem.sub hsum
  apply herror.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hi (j : ℕ) : Integrable
      (fun x ↦ p j (fun _ ↦ x) * Real.exp (-(n : ℝ) * Q x)) :=
    integrable_multilinear_gaussian (p j) hQc hb hQb hn0
  have hhI : IntegrableOn (fun x ↦ h x * Real.exp (-(n : ℝ) * Q x)) K := by
    apply IntegrableOn.mono_set (t := L) _ hKL
    apply ContinuousOn.integrableOn_compact hL
    exact hh.mul (by fun_prop)
  have hpsum : IntegrableOn
      (fun x ↦ p.partialSum N x * Real.exp (-(n : ℝ) * Q x)) K := by
    apply IntegrableOn.mono_set (t := L) _ hKL
    apply ContinuousOn.integrableOn_compact hL
    exact (p.partialSum_continuous N).continuousOn.mul (by fun_prop)
  have hremEq : (∫ x in K, (h x - p.partialSum N x) * Real.exp (-(n : ℝ) * Q x)) =
      (∫ x in K, h x * Real.exp (-(n : ℝ) * Q x)) -
        ∑ j ∈ Finset.range N, ∫ x in K, p j (fun _ ↦ x) * Real.exp (-(n : ℝ) * Q x) := by
    simp_rw [sub_mul]
    rw [integral_sub hhI hpsum]
    congr 1
    simp_rw [FormalMultilinearSeries.partialSum, Finset.sum_mul]
    exact integral_finsetSum _ (fun j _ ↦ (hi j).integrableOn)
  have hcoeff (j : ℕ) :
      (n : ℝ) ^ (-((Module.finrank ℝ V : ℝ) + j) / 2) * gaussianAmplitudeCoefficient p Q j =
      (∫ x in K, p j (fun _ ↦ x) * Real.exp (-(n : ℝ) * Q x)) +
        ∫ x in Kᶜ, p j (fun _ ↦ x) * Real.exp (-(n : ℝ) * Q x) := by
    unfold gaussianAmplitudeCoefficient
    rw [← multilinear_gaussian_integral (p j) hQs hn0]
    exact (integral_add_compl hK (hi j)).symm
  simp only [Finset.sum_apply]
  rw [hremEq]
  simp_rw [hcoeff]
  rw [Finset.sum_add_distrib]
  ring

end OdlyzkoPoonen
