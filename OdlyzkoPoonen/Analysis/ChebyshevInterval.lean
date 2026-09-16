import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# A prime-product interval from Chebyshev bounds

The elementary lower bound for the Chebyshev theta function is eventually at
least `(log 2)/2` times its argument. Subtracting the upper bound at `x` from
the lower bound at `8x` gives `theta(8x)-theta(x) >= x` eventually. This proves
the needed abundance of primes on a fixed-ratio interval without a prime
number theorem assumption. All thresholds are absolute.
-/

namespace OdlyzkoPoonen
open Filter
open scoped Topology

lemma tendsto_log_div_sqrt_atTop :
    Tendsto (fun x : ℝ ↦ Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  simpa only [← Real.sqrt_eq_rpow] using h

lemma eventually_theta_ge_half_log_two_mul :
    ∀ᶠ x : ℝ in atTop, (Real.log 2 / 2) * x ≤ Chebyshev.theta x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : Tendsto (fun x : ℝ ↦ (Real.log 2 + Real.log 3) / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0)).const_mul
        (Real.log 2 + Real.log 3)
  have hl : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hc.eventually_le_const (by positivity : 0 < Real.log 2 / 6),
    hl.eventually_le_const (by positivity : 0 < Real.log 2 / 6),
    tendsto_log_div_sqrt_atTop.eventually_le_const (by positivity : 0 < Real.log 2 / 12)]
    with x hx hcx hlx hsx
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hc' := (div_le_iff₀ hx0).mp hcx
  have hl' := (div_le_iff₀ hx0).mp hlx
  have hs' := (div_le_iff₀ hs0).mp hsx
  have hsbound : 2 * Real.sqrt x * Real.log x ≤ (Real.log 2 / 6) * x := by
    calc
      _ ≤ 2 * Real.sqrt x * ((Real.log 2 / 12) * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hs' (by positivity)
      _ = (Real.log 2 / 6) * (Real.sqrt x) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hx0.le]
  have hshift : Real.log (x + 2) ≤ Real.log 3 + Real.log x := by
    have h := Real.log_le_log (by linarith : 0 < x + 2)
      (by linarith : x + 2 ≤ 3 * x)
    rwa [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hx0.ne'] at h
  have htheta := Chebyshev.theta_ge' hx
  nlinarith

lemma eventually_theta_eight_mul_sub_ge :
    ∀ᶠ x : ℝ in atTop, x ≤ Chebyshev.theta (8 * x) - Chebyshev.theta x := by
  have ht : Tendsto (fun x : ℝ ↦ 8 * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 8)).mpr tendsto_id
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    ht.eventually eventually_theta_ge_half_log_two_mul] with x hx hlower
  have hupper := Chebyshev.theta_le_log4_mul_x hx
  rw [hlog4] at hupper
  nlinarith [mul_nonneg (sub_nonneg.mpr hlog) hx]

lemma exists_threshold_theta_eight_mul_sub_ge :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      x ≤ Chebyshev.theta (8 * x) - Chebyshev.theta x := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp eventually_theta_eight_mul_sub_ge
  exact ⟨max 1 x₀, le_max_left _ _, fun x hx ↦ hx₀ x ((le_max_right _ _).trans hx)⟩

end OdlyzkoPoonen
