import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Extending an exponential probability estimate to every degree

An eventual logarithmic exponential bound for a function bounded by one extends
to all degrees at least three by one absolute multiplicative constant.
-/

namespace OdlyzkoPoonen

lemma extend_logarithmic_exponential_bound {f : ℕ → ℝ} {a : ℝ}
    (ha : 0 < a) (hunit : ∀ n, f n ≤ 1) {N : ℕ}
    (hbound : ∀ n, N ≤ n → f n ≤ Real.exp (-a * n / Real.log (n : ℝ) ^ 4)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      f n ≤ C * Real.exp (-a * n / Real.log (n : ℝ) ^ 4) := by
  let C := Real.exp (a * N / Real.log 3 ^ 4)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hC1 : 1 ≤ C := Real.one_le_exp_iff.mpr (by positivity)
  refine ⟨C, Real.exp_pos _, ?_⟩
  intro n hn
  by_cases hN : N ≤ n
  · exact (hbound n hN).trans (le_mul_of_one_le_left (Real.exp_pos _).le hC1)
  · have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : Real.log (3 : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by norm_num) hnR
    have hrate : (n : ℝ) / Real.log (n : ℝ) ^ 4 ≤ (N : ℝ) / Real.log 3 ^ 4 := by
      calc
        _ ≤ (n : ℝ) / Real.log 3 ^ 4 := div_le_div_of_nonneg_left
          (Nat.cast_nonneg n) (by positivity) (pow_le_pow_left₀ hlog3.le hlog _)
        _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast (show n ≤ N by omega))
          (by positivity)
    refine (hunit n).trans ?_
    rw [show C = Real.exp (a * N / Real.log 3 ^ 4) from rfl, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    have h := mul_le_mul_of_nonneg_left hrate ha.le
    calc
      0 ≤ a * ((N : ℝ) / Real.log 3 ^ 4) - a * ((n : ℝ) / Real.log (n : ℝ) ^ 4) :=
        sub_nonneg.mpr h
      _ = _ := by ring

end OdlyzkoPoonen
