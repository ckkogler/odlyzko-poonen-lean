import OdlyzkoPoonen.Analysis.GaussianScaling
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# Polynomial packaging of binomial half powers

After substituting `x = 1 / sqrt(n)`, a binomial coefficient times a sufficiently
high inverse half power becomes an ordinary polynomial in `x`. This collects
the moment expansion without introducing parameter-dependent coefficients.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

lemma cast_factorial_mul_choose_eq_prod (n r : ℕ) (hr : r ≤ n) :
    (r.factorial : ℝ) * (n.choose r : ℝ) = ∏ t ∈ Finset.range r, ((n : ℝ) - t) := by
  rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro t ht
  rw [Nat.cast_sub (by have := Finset.mem_range.mp ht; omega)]

lemma binomial_times_inverse_square (n r : ℕ) (hr : r ≤ n) {x : ℝ}
    (hx : (n : ℝ) * x ^ 2 = 1) :
    (r.factorial : ℝ) * (n.choose r : ℝ) * x ^ (2 * r) =
      ∏ t ∈ Finset.range r, (1 - (t : ℝ) * x ^ 2) := by
  rw [cast_factorial_mul_choose_eq_prod n r hr, pow_mul]
  have hp : (x ^ 2) ^ r = ∏ _t ∈ Finset.range r, x ^ 2 := by simp
  rw [hp, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t _
  rw [sub_mul, hx]

/-- A single binomial-weighted half-power term, as an ordinary polynomial. -/
noncomputable def binomialHalfPowerPolynomial (k r : ℕ) (a : ℝ) : ℝ[X] :=
  C (a / r.factorial) * X ^ (k - 2 * r) *
    ∏ t ∈ Finset.range r, (1 - C (t : ℝ) * X ^ 2)

lemma binomialHalfPowerPolynomial_eval (n k r : ℕ) (hr : r ≤ n) (hk : 2 * r ≤ k)
    (a x : ℝ) (hx : (n : ℝ) * x ^ 2 = 1) :
    (binomialHalfPowerPolynomial k r a).eval x = (n.choose r : ℝ) * a * x ^ k := by
  simp only [binomialHalfPowerPolynomial, eval_mul, eval_C, eval_pow, eval_X,
    eval_prod, eval_sub, eval_one]
  rw [← binomial_times_inverse_square n r hr hx]
  have hfac : (r.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr r.factorial_ne_zero
  calc
    _ = (n.choose r : ℝ) * a * (x ^ (k - 2 * r) * x ^ (2 * r)) := by field_simp
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hk]

lemma binomialHalfPowerPolynomial_coeff_zero (k r : ℕ) (hk : 2 * r < k) (a : ℝ) :
    (binomialHalfPowerPolynomial k r a).coeff 0 = 0 := by
  have hp : k - 2 * r ≠ 0 := by omega
  have he : (binomialHalfPowerPolynomial k r a).eval 0 = 0 := by
    simp only [binomialHalfPowerPolynomial, eval_mul, eval_C, eval_pow, eval_X,
      zero_pow hp, mul_zero, zero_mul]
  rw [coeff_zero_eq_eval_zero]
  exact he

theorem binomialHalfPowerPolynomial_eval_inverse_sqrt (n k r : ℕ)
    (hn : 1 ≤ n) (hr : r ≤ n) (hk : 2 * r ≤ k) (a : ℝ) :
    (binomialHalfPowerPolynomial k r a).eval ((Real.sqrt (n : ℝ))⁻¹) =
      (n.choose r : ℝ) * a * (n : ℝ) ^ (-(k : ℝ) / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx : (n : ℝ) * (Real.sqrt (n : ℝ))⁻¹ ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt hn0.le, mul_inv_cancel₀ hn0.ne']
  rw [binomialHalfPowerPolynomial_eval n k r hr hk a _ hx, inv_pow,
    inverse_sqrt_pow_eq_rpow hn0.le]

end OdlyzkoPoonen
