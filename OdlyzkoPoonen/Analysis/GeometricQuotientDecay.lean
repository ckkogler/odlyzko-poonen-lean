import OdlyzkoPoonen.Arithmetic.SparseQuotientBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Geometric decay with a quarter-degree integer exponent

The floor exponent in the companion estimate still gives exponential decay.
Consequently its contribution is smaller than every prescribed real power.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped Topology

lemma eventually_geometric_quarter_le_exp {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ᶠ n : ℕ in atTop, b ^ ((n - 1) / 4) ≤
      Real.exp (-(-Real.log b / 16) * (n : ℝ)) := by
  filter_upwards [eventually_ge_atTop 5] with n hn
  have hquot := nat_div_ge_half_real_ratio (by norm_num : 0 < 4)
    (by omega : 4 ≤ n - 1)
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : (n : ℝ) / 16 ≤ (((n - 1) / 4 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hquot
    norm_num at hquot
    linarith
  have hlog : Real.log b < 0 := Real.log_neg hb0 hb1
  calc
    _ = Real.exp ((((n - 1) / 4 : ℕ) : ℝ) * Real.log b) := by
      rw [Real.exp_nat_mul, Real.exp_log hb0]
    _ ≤ Real.exp (((n : ℝ) / 16) * Real.log b) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hk hlog.le)
    _ = _ := by congr 1; ring

lemma geometric_quarter_isBigO_rpow {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (A : ℝ) :
    (fun n : ℕ ↦ b ^ ((n - 1) / 4)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
  have hc : 0 < -Real.log b / 16 := div_pos (neg_pos.mpr (Real.log_neg hb0 hb1)) (by norm_num)
  have hexp : (fun n : ℕ ↦ Real.exp (-(-Real.log b / 16) * (n : ℝ))) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
    simpa only [Function.comp_def] using
      ((isLittleO_exp_neg_mul_rpow_atTop hc (-A)).comp_tendsto
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)).isBigO
  refine (Asymptotics.IsBigO.of_norm_eventuallyLE ?_).trans hexp
  filter_upwards [eventually_geometric_quarter_le_exp hb0 hb1] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hb0.le _),
    abs_of_nonneg (Real.exp_pos _).le] using hn

end OdlyzkoPoonen
