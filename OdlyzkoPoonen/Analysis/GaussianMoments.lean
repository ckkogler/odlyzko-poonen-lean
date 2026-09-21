import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic

/-!
# Polynomial moments of finite-dimensional Gaussians

A fixed polynomial weight can be absorbed by a weaker Gaussian. The bounds
give integrability of every norm moment and of continuous functions with
polynomial growth against a coercive quadratic exponential.
-/

namespace OdlyzkoPoonen
open MeasureTheory

lemma even_power_mul_gaussian_le (m : ℕ) {b x : ℝ} (hb : 0 < b) :
    x ^ (2 * m) * Real.exp (-b * x ^ 2) ≤
      ((m.factorial : ℝ) / (b / 2) ^ m) * Real.exp (-(b / 2) * x ^ 2) := by
  have he := Real.pow_div_factorial_le_exp ((b / 2) * x ^ 2)
    (by positivity : 0 ≤ (b / 2) * x ^ 2) m
  have hfac : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  have hb2 : (b / 2) ≠ 0 := ne_of_gt (by linarith)
  calc
    _ = (((b / 2) * x ^ 2) ^ m / (m.factorial : ℝ)) *
        ((m.factorial : ℝ) / (b / 2) ^ m) * Real.exp (-b * x ^ 2) := by
      rw [mul_pow, ← pow_mul]
      field_simp
    _ ≤ Real.exp ((b / 2) * x ^ 2) *
        ((m.factorial : ℝ) / (b / 2) ^ m) * Real.exp (-b * x ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right he (by positivity)) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_comm (Real.exp ((b / 2) * x ^ 2)), mul_assoc, ← Real.exp_add]
      congr 2
      ring

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma integrable_gaussian_norm_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : V ↦ Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := (b : ℂ)) (show 0 < (b : ℂ).re from hb) 0 (0 : V)).re
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, RCLike.re_to_complex, Complex.exp_ofReal_re] using h

lemma integrable_norm_even_pow_mul_gaussian (m : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : V ↦ ‖x‖ ^ (2 * m) * Real.exp (-b * ‖x‖ ^ 2)) := by
  have hg := (integrable_gaussian_norm_sq (V := V) (b := b / 2) (by linarith)).const_mul
    ((m.factorial : ℝ) / (b / 2) ^ m)
  apply hg.mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact even_power_mul_gaussian_le m hb

theorem integrable_norm_pow_mul_gaussian (m : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : V ↦ ‖x‖ ^ m * Real.exp (-b * ‖x‖ ^ 2)) := by
  have hg := (integrable_gaussian_norm_sq (V := V) hb).add
    (integrable_norm_even_pow_mul_gaussian (V := V) m hb)
  apply hg.mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hm : ‖x‖ ^ m ≤ 1 + ‖x‖ ^ (2 * m) := by
    rw [show 2 * m = m * 2 by omega, pow_mul]
    nlinarith [sq_nonneg (‖x‖ ^ m - 1)]
  simpa only [Pi.add_apply, add_mul, one_mul] using!
    mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le

/-- Polynomial growth remains integrable under a coercive Gaussian bound. -/
theorem integrable_polynomial_growth_mul_gaussian {h Q : V → ℝ}
    (hh : Continuous h) (hQ : Continuous Q) {b C : ℝ} (hb : 0 < b)
    (m : ℕ) (hbound : ∀ x, |h x| ≤ C * ‖x‖ ^ m)
    (hcoercive : ∀ x, b * ‖x‖ ^ 2 ≤ Q x) :
    Integrable (fun x ↦ h x * Real.exp (-Q x)) := by
  have hg := (integrable_norm_pow_mul_gaussian (V := V) m hb).const_mul C
  apply hg.mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ |h x| * Real.exp (-b * ‖x‖ ^ 2) := by
      gcongr
      linarith [hcoercive x]
    _ ≤ (C * ‖x‖ ^ m) * Real.exp (-b * ‖x‖ ^ 2) := by gcongr; exact hbound x
    _ = _ := by ring

end
end OdlyzkoPoonen
