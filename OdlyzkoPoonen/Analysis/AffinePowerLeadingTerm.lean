import OdlyzkoPoonen.Analysis.AffineHalfPowerExpansion
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Leading real-power asymptotics under affine changes of index

An analytic expansion of `(1-s/x)^a` at inverse infinity quantifies the effect
of a fixed offset. The remainder improves the power by one.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped Topology ContDiff

lemma analytic_sub_value_isBigO {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    (fun x ↦ f x - f 0) =O[𝓝 0] (fun x : ℝ ↦ x) := by
  obtain ⟨p, hp⟩ := hf
  have he := hp.isBigO_sub_partialSum_pow 1
  simp only [zero_add, FormalMultilinearSeries.partialSum, Finset.sum_range_one,
    hp.coeff_zero, pow_one] at he
  exact he.of_norm_right

lemma affine_power_analyticAt (s a : ℝ) : AnalyticAt ℝ (fun x : ℝ ↦ (1 - s * x) ^ a) 0 := by
  have hi : ContDiffAt ℝ ω (fun x : ℝ ↦ 1 - s * x) 0 := by fun_prop
  have ho : ContDiffAt ℝ ω (fun y : ℝ ↦ y ^ a) (1 - s * 0) :=
    Real.contDiffAt_rpow_const_of_ne (by norm_num)
  have he := ho.comp (0 : ℝ) hi
  simpa only [Function.comp_def] using! he.analyticAt

lemma affine_power_inverse_error (s a : ℝ) :
    (fun n : ℕ ↦ (1 - s / (n : ℝ)) ^ a - 1) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ)⁻¹) := by
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have he := (analytic_sub_value_isBigO (affine_power_analyticAt s a)).comp_tendsto ht
  simpa only [Function.comp_def, mul_zero, sub_zero, Real.one_rpow, div_eq_mul_inv] using he

/-- Changing from `k` to `q*k+s` changes the leading power by an error of one lower order. -/
theorem affine_rpow_leading_error {q : ℕ} (hq : 0 < q) (s : ℕ) (a : ℝ) :
    (fun k : ℕ ↦ (k : ℝ) ^ a - (q : ℝ) ^ (-a) * ((q * k + s : ℕ) : ℝ) ^ a)
      =O[atTop] (fun k : ℕ ↦ ((q * k + s : ℕ) : ℝ) ^ (a - 1)) := by
  have he := (affine_power_inverse_error s a).comp_tendsto (nat_affine_tendsto hq s)
  have hm := (isBigO_refl (fun k : ℕ ↦ ((q * k + s : ℕ) : ℝ) ^ a) atTop).mul he
  have hprod : (fun k : ℕ ↦ ((q * k + s : ℕ) : ℝ) ^ a * ((q * k + s : ℕ) : ℝ)⁻¹)
      =ᶠ[atTop] (fun k : ℕ ↦ ((q * k + s : ℕ) : ℝ) ^ (a - 1)) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hn : (0 : ℝ) < (q * k + s : ℕ) := by
      exact_mod_cast (show 0 < q * k + s by positivity)
    rw [Real.rpow_sub hn, Real.rpow_one, div_eq_mul_inv]
  have hc := (hm.congr' Filter.EventuallyEq.rfl hprod).const_mul_left ((q : ℝ) ^ (-a))
  apply hc.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hn : (0 : ℝ) < (q * k + s : ℕ) := by positivity
  have hfac : 1 - (s : ℝ) / (q * k + s : ℕ) =
      (q : ℝ) * k / (q * k + s : ℕ) := by
    push_cast
    field_simp
    ring
  dsimp only [Function.comp_def]
  rw [hfac, Real.div_rpow (mul_nonneg hq'.le hk'.le) hn.le, Real.mul_rpow hq'.le hk'.le]
  have hqa : (q : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos hq' a).ne'
  have hna : ((q * k + s : ℕ) : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos hn a).ne'
  rw [Real.rpow_neg hq'.le]
  field_simp

end OdlyzkoPoonen
