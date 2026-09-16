import OdlyzkoPoonen.Analysis.LogarithmicDomination
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# A logarithmic cutoff gives every polynomial decay rate

The ceiling loses at most one in the cutoff. Its square is dominated by the
fixed-factor exponential decay, while the reciprocal tail is a direct real
power identity. These lemmas retain real exponents and the exact ceiling.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped Topology

lemma eventually_exp_cutoff_cost_le_rpow {a C A : ℝ} (ha : 0 < a)
    (hC : 0 ≤ C) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (4 * (⌈C * Real.log (n : ℝ)⌉₊ : ℝ) ^ 2 -
        a * (n : ℝ) / Real.log (n : ℝ) ^ 4) ≤ (n : ℝ) ^ (-A) := by
  have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, ht.eventually_ge_atTop 1,
    eventually_log_pow_le_nat_div_log_pow (4 * (C + 1) ^ 2 + A) ha 2 4] with n hn hlog hdom
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hC hlog0)
  have hupper : (⌈C * Real.log (n : ℝ)⌉₊ : ℝ) ≤ (C + 1) * Real.log (n : ℝ) := by
    nlinarith
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg ⌈C * Real.log (n : ℝ)⌉₊) hupper 2
  have hlogsq : Real.log (n : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by nlinarith
  have hAlog := mul_le_mul_of_nonneg_left hlogsq hA
  rw [Real.rpow_def_of_pos hn0]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma two_rpow_neg_half_ceil_log_le {n : ℕ} (hn : 0 < n) (A : ℝ) :
    (2 : ℝ) ^ (-(⌈(2 * A / Real.log 2) * Real.log (n : ℝ)⌉₊ : ℝ) / 2) ≤
      (n : ℝ) ^ (-A) := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hceil := Nat.le_ceil ((2 * A / Real.log 2) * Real.log (n : ℝ))
  have h := mul_le_mul_of_nonneg_left hceil hl2.le
  have he : Real.log 2 * ((2 * A / Real.log 2) * Real.log (n : ℝ)) =
      2 * A * Real.log (n : ℝ) := by field_simp
  rw [he] at h
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma isBigO_rpow_of_reciprocal_finite_bound {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) {a : ℝ} (ha : 0 < a) {N : ℕ}
    (hbound : ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
      f n ≤ Real.exp (4 * (L : ℝ) ^ 2 - a * (n : ℝ) / Real.log (n : ℝ) ^ 4) +
        6 * (2 : ℝ) ^ (-(L : ℝ) / 2)) (A : ℝ) (hA : 0 < A) :
    f =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
  let C := 2 * A / Real.log 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine Asymptotics.isBigO_iff.mpr ⟨7, ?_⟩
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1,
    eventually_exp_cutoff_cost_le_rpow ha hC hA.le] with n hn hn1 hfirst
  have hfinite := hbound n hn ⌈C * Real.log (n : ℝ)⌉₊
  have htail := two_rpow_neg_half_ceil_log_le (by omega : 0 < n) A
  change (2 : ℝ) ^ (-(⌈C * Real.log (n : ℝ)⌉₊ : ℝ) / 2) ≤ (n : ℝ) ^ (-A) at htail
  simp only [Real.norm_eq_abs, abs_of_nonneg (hf n),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (-A))]
  linarith

end OdlyzkoPoonen
