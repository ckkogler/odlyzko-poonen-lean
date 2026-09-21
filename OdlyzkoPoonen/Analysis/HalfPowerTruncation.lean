import OdlyzkoPoonen.Analysis.BinomialHalfPowerPolynomial
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Truncating polynomial half-power expansions

Division by a power of `X` removes exactly the terms below the chosen error
scale. The quotient stays bounded near zero, so evaluation at `1/sqrt(n)`
turns the discarded polynomial multiple into the required inverse power.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics
open scoped BigOperators Topology

lemma tendsto_inverse_sqrt_nat :
    Tendsto (fun n : ℕ ↦ (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

lemma polynomial_mod_power_remainder_isBigO (P : ℝ[X]) (N : ℕ) :
    (fun x : ℝ ↦ P.eval x - (P %ₘ X ^ N).eval x) =O[𝓝 0] (fun x : ℝ ↦ x ^ N) := by
  have hq : (fun x : ℝ ↦ (P /ₘ X ^ N).eval x) =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    (P /ₘ X ^ N).continuousAt.isBigO_one ℝ
  have he (x : ℝ) : P.eval x - (P %ₘ X ^ N).eval x = x ^ N * (P /ₘ X ^ N).eval x := by
    have h := congrArg (fun p : ℝ[X] ↦ p.eval x) (modByMonic_add_div P (X ^ N))
    simp only [eval_add, eval_mul, eval_pow, eval_X] at h
    linarith
  simpa only [he, mul_one] using (isBigO_refl (fun x : ℝ ↦ x ^ N) (𝓝 0)).mul hq

theorem polynomial_halfpower_truncation (P : ℝ[X]) (N : ℕ) (hN : 1 ≤ N) :
    let Q := P %ₘ X ^ N
    Q.natDegree < N ∧ Q.coeff 0 = P.coeff 0 ∧
      (fun n : ℕ ↦ P.eval ((Real.sqrt (n : ℝ))⁻¹) - Q.eval ((Real.sqrt (n : ℝ))⁻¹))
        =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-(N : ℝ) / 2)) := by
  dsimp only
  have hN0 : N ≠ 0 := by omega
  constructor
  · have h := natDegree_modByMonic_lt P (monic_X_pow N) (show (X ^ N : ℝ[X]) ≠ 1 by
      intro he
      have hd := congrArg natDegree he
      simp only [natDegree_X_pow, natDegree_one] at hd
      omega)
    simpa only [natDegree_X_pow] using h
  constructor
  · have he := congrArg (fun p : ℝ[X] ↦ p.eval 0) (modByMonic_add_div P (X ^ N))
    simpa only [eval_add, eval_mul, eval_pow, eval_X, zero_pow hN0, zero_mul, add_zero,
      ← coeff_zero_eq_eval_zero] using he
  · have he := (polynomial_mod_power_remainder_isBigO P N).comp_tendsto tendsto_inverse_sqrt_nat
    simpa only [Function.comp_def, inv_pow, inverse_sqrt_pow_eq_rpow (Nat.cast_nonneg _)] using he

lemma polynomial_eval_inverse_sqrt_eq_half_power_sum (P : ℝ[X]) {N : ℕ}
    (hN : P.natDegree < N) (n : ℕ) :
    P.eval ((Real.sqrt (n : ℝ))⁻¹) =
      ∑ j ∈ Finset.range N, P.coeff j * (n : ℝ) ^ (-(j : ℝ) / 2) := by
  rw [eval_eq_sum_range' hN]
  simp only [inv_pow, inverse_sqrt_pow_eq_rpow (Nat.cast_nonneg _)]

end OdlyzkoPoonen
