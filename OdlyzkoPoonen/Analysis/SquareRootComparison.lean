import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Quantitative square-root comparisons

These real-variable estimates compare the square-root leading terms for adjacent
odd and even degrees, and transfer inverse three-halves bounds between comparable
positive arguments. They contain no probability or polynomial hypotheses.
-/

namespace OdlyzkoPoonen

lemma inverse_sqrt_pi_le {x : ℝ} (hx : 0 < x) :
    1 / Real.sqrt (Real.pi * x) ≤ 1 / Real.sqrt x := by
  apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr hx)
  apply Real.sqrt_le_sqrt
  calc
    x = 1 * x := by ring
    _ ≤ Real.pi * x := mul_le_mul_of_nonneg_right (by linarith [Real.two_le_pi]) hx.le

lemma sqrt_two_div_double (x : ℝ) :
    Real.sqrt (2 / (Real.pi * (2 * x))) = 1 / Real.sqrt (Real.pi * x) := by
  have he : 2 / (Real.pi * (2 * x)) = 1 / (Real.pi * x) := by ring
  rw [he, Real.sqrt_div (by positivity), Real.sqrt_one]

lemma sqrt_odd_degree_comparison {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 / Real.sqrt (Real.pi * x) - Real.sqrt (2 / (Real.pi * (2 * x + 1))) ∧
      1 / Real.sqrt (Real.pi * x) - Real.sqrt (2 / (Real.pi * (2 * x + 1))) ≤
        (1 / Real.sqrt (Real.pi * x)) / (2 * x + 1) := by
  let t := 1 / Real.sqrt (Real.pi * x)
  let u := Real.sqrt (2 / (Real.pi * (2 * x + 1)))
  have ht : 0 < t := by dsimp [t]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have ht2 : t ^ 2 = 1 / (Real.pi * x) := by
    dsimp [t]
    rw [div_pow, Real.sq_sqrt (by positivity), one_pow]
  have hu2 : u ^ 2 = 2 / (Real.pi * (2 * x + 1)) := by
    dsimp [u]
    rw [Real.sq_sqrt (by positivity)]
  have hd : 2 / (Real.pi * (2 * x + 1)) ≤ 1 / (Real.pi * x) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [Real.pi_pos]
  have hut : u ≤ t := by nlinarith
  have hs : t ^ 2 - u ^ 2 = t ^ 2 / (2 * x + 1) := by
    rw [ht2, hu2]
    field_simp
    ring
  have hmul : t * (t - u) ≤ t ^ 2 / (2 * x + 1) := by
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hut)]
  have he : t ^ 2 / (2 * x + 1) = t * (t / (2 * x + 1)) := by ring
  rw [he] at hmul
  exact ⟨sub_nonneg.mpr hut, (mul_le_mul_iff_right₀ ht).mp hmul⟩

lemma inverse_three_halves_comparison {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hyx : y ≤ 3 * x) :
    3 / (x * Real.sqrt x) ≤ 18 / (y * Real.sqrt y) := by
  have hs : Real.sqrt y ≤ 2 * Real.sqrt x := by
    have hxs := Real.sq_sqrt hx.le
    have hys := Real.sq_sqrt hy.le
    have hxp := Real.sqrt_nonneg x
    have hyp := Real.sqrt_nonneg y
    nlinarith
  have hm : y * Real.sqrt y ≤ 6 * (x * Real.sqrt x) := by
    calc
      y * Real.sqrt y ≤ (3 * x) * (2 * Real.sqrt x) :=
        mul_le_mul hyx hs (Real.sqrt_nonneg y) (by positivity)
      _ = 6 * (x * Real.sqrt x) := by ring
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

lemma rpow_neg_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (-3 / 2 : ℝ) = 1 / (x * Real.sqrt x) := by
  rw [show (-3 / 2 : ℝ) = -(1 + 1 / 2) by norm_num, Real.rpow_neg hx.le,
    Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]

end OdlyzkoPoonen
