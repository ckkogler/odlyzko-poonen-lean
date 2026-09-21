import OdlyzkoPoonen.Analysis.GaussianMoments
import OdlyzkoPoonen.Analysis.GaussianScaling
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Gaussian integral bounds with explicit decay exponents

Polynomial pointwise remainders integrate to half-integer powers. The same
estimate controls tails outside any fixed neighborhood of the origin.
-/

namespace OdlyzkoPoonen
open MeasureTheory Filter Asymptotics
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma norm_gaussian_moment_scale (N : ℕ) (b : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ x : V, ‖x‖ ^ N * Real.exp (-(r * b) * ‖x‖ ^ 2)) =
      r ^ (-((Module.finrank ℝ V : ℝ) + N) / 2) *
        ∫ x : V, ‖x‖ ^ N * Real.exp (-b * ‖x‖ ^ 2) := by
  have hh (t : ℝ) (ht : 0 < t) (x : V) : ‖t • x‖ ^ N = t ^ N * ‖x‖ ^ N := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow]
  have hQ (t : ℝ) (ht : 0 < t) (x : V) :
      b * ‖t • x‖ ^ 2 = t ^ 2 * (b * ‖x‖ ^ 2) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    ring
  simpa only [neg_mul, mul_assoc] using
    homogeneous_gaussian_integral_half_power (h := fun x : V ↦ ‖x‖ ^ N)
      (Q := fun x ↦ b * ‖x‖ ^ 2) N hh hQ hr

/-- A pointwise Gaussian majorant gives its exact integrated decay rate. -/
theorem abs_setIntegral_le_gaussian_moment {K : Set V} (hK : MeasurableSet K)
    {f : V → ℝ} (N : ℕ) {C b r : ℝ} (hC : 0 ≤ C) (hb : 0 < b) (hr : 0 < r)
    (hf : ∀ x ∈ K, |f x| ≤ C * (‖x‖ ^ N * Real.exp (-(r * b) * ‖x‖ ^ 2))) :
    |∫ x in K, f x| ≤ C * r ^ (-((Module.finrank ℝ V : ℝ) + N) / 2) *
      ∫ x : V, ‖x‖ ^ N * Real.exp (-b * ‖x‖ ^ 2) := by
  have hg := (integrable_norm_pow_mul_gaussian (V := V) N (mul_pos hr hb)).const_mul C
  calc
    _ ≤ ∫ x in K, C * (‖x‖ ^ N * Real.exp (-(r * b) * ‖x‖ ^ 2)) := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hg.integrableOn
      exact (ae_restrict_iff' hK).mpr (Eventually.of_forall fun x hx ↦ by
        simpa only [Real.norm_eq_abs] using hf x hx)
    _ ≤ ∫ x : V, C * (‖x‖ ^ N * Real.exp (-(r * b) * ‖x‖ ^ 2)) :=
      setIntegral_le_integral hg (Eventually.of_forall fun x ↦ by positivity)
    _ = _ := by rw [integral_const_mul, norm_gaussian_moment_scale N b hr, mul_assoc]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma norm_power_tail_bound {ε : ℝ} (hε : 0 < ε) {j N : ℕ} (hj : j ≤ N)
    {x : V} (hx : ε ≤ ‖x‖) :
    ‖x‖ ^ j ≤ (ε ^ (N - j))⁻¹ * ‖x‖ ^ N := by
  have hp : ε ^ (N - j) ≤ ‖x‖ ^ (N - j) := pow_le_pow_left₀ hε.le hx _
  apply (mul_le_mul_iff_right₀ (pow_pos hε (N - j))).mp
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hε.ne'), one_mul]
  calc
    ε ^ (N - j) * ‖x‖ ^ j ≤ ‖x‖ ^ (N - j) * ‖x‖ ^ j := by gcongr
    _ = ‖x‖ ^ N := by rw [← pow_add, Nat.sub_add_cancel hj]

/-- Every polynomial order is available for a Gaussian tail away from zero. -/
theorem abs_gaussian_tail_le {K : Set V} (hK : MeasurableSet K)
    {h Q : V → ℝ} {ε b C r : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (hC : 0 ≤ C) (hr : 0 < r) (j N : ℕ) (hj : j ≤ N)
    (hball : Metric.ball 0 ε ⊆ K)
    (hh : ∀ x, |h x| ≤ C * ‖x‖ ^ j)
    (hQ : ∀ x, b * ‖x‖ ^ 2 ≤ Q x) :
    |∫ x in Kᶜ, h x * Real.exp (-r * Q x)| ≤
      (C * (ε ^ (N - j))⁻¹) * r ^ (-((Module.finrank ℝ V : ℝ) + N) / 2) *
        ∫ x : V, ‖x‖ ^ N * Real.exp (-b * ‖x‖ ^ 2) := by
  apply abs_setIntegral_le_gaussian_moment hK.compl N (by positivity) hb hr
  intro x hx
  have hεx : ε ≤ ‖x‖ := by
    by_contra! he
    exact hx (hball (by simpa only [Metric.mem_ball, dist_zero_right] using he))
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (C * ‖x‖ ^ j) * Real.exp (-(r * b) * ‖x‖ ^ 2) := by
      apply mul_le_mul (hh x) _ (Real.exp_pos _).le (mul_nonneg hC (pow_nonneg (norm_nonneg _) _))
      apply Real.exp_le_exp.mpr
      nlinarith [hQ x]
    _ ≤ (C * ((ε ^ (N - j))⁻¹ * ‖x‖ ^ N)) *
        Real.exp (-(r * b) * ‖x‖ ^ 2) := by
      gcongr
      exact norm_power_tail_bound hε hj hεx
    _ = _ := by ring

end OdlyzkoPoonen
