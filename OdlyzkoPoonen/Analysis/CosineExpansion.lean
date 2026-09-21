import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# A uniform quartic remainder for cosine

The fourth derivative is bounded by one on every interval. Taylor's theorem
therefore gives a global quartic error, including both signs of the argument.
-/

namespace OdlyzkoPoonen
open Set Filter Asymptotics
open scoped Topology

lemma cosine_taylor_three {x : ℝ} (hx : x ≠ 0) :
    taylorWithinEval Real.cos 3 (uIcc 0 x) 0 x = 1 - x ^ 2 / 2 := by
  rw [taylor_within_apply]
  have hd (j : ℕ) : iteratedDerivWithin j Real.cos (uIcc 0 x) 0 =
      iteratedDeriv j Real.cos 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx.symm)
      Real.contDiff_cos.contDiffAt left_mem_uIcc
  simp_rw [hd]
  norm_num [Finset.sum_range_succ, Real.iteratedDeriv_add_one_cos,
    Real.iteratedDeriv_add_one_sin]
  ring

theorem cosine_quadratic_remainder_bound (x : ℝ) :
    |Real.cos x - (1 - x ^ 2 / 2)| ≤ x ^ 4 / 24 := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨c, _, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.cos) (n := 3) (Ne.symm hx) (by fun_prop)
  rw [cosine_taylor_three hx] at he
  rw [he]
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat, sub_zero]
  rw [abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
  have h := Real.abs_iteratedDeriv_cos_le_one 4 c
  calc
    _ ≤ 1 * |x| ^ 4 / 24 := by gcongr
    _ = _ := by rw [one_mul, pow_abs, abs_of_nonneg (by positivity)]

theorem cosine_quadratic_remainder_isBigO :
    (fun x : ℝ ↦ Real.cos x - (1 - x ^ 2 / 2)) =O[𝓝 0]
      (fun x : ℝ ↦ |x| ^ 4) := by
  refine isBigO_iff.mpr ⟨1 / 24, Filter.Eventually.of_forall ?_⟩
  intro x
  have hp : 0 ≤ |x| ^ 4 := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp, pow_abs,
    abs_of_nonneg (show 0 ≤ x ^ 4 by positivity), div_eq_mul_inv, one_mul, mul_comm]
    using cosine_quadratic_remainder_bound x

end OdlyzkoPoonen
