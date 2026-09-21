import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Finite expansions of powers with a uniform remainder

Taylor's theorem for the scalar polynomial `x^n` controls the truncation by
the largest endpoint, rather than by the sum of absolute terms. In particular,
a Gaussian bound for both endpoints survives taking large powers.
-/

namespace OdlyzkoPoonen
open scoped BigOperators
open Set

/-- The first `R` terms of the expansion of `a^n` around `b`. -/
noncomputable def truncatedPowerExpansion (n R : ℕ) (a b : ℝ) : ℝ :=
  ∑ r ∈ Finset.range R, (n.choose r : ℝ) * b ^ (n - r) * (a - b) ^ r

lemma truncatedPowerExpansion_self (n R : ℕ) (hR : 1 ≤ R) (a : ℝ) :
    truncatedPowerExpansion n R a a = a ^ n := by
  unfold truncatedPowerExpansion
  rw [Finset.sum_eq_single 0]
  · simp
  · intro r _ hr
    simp [zero_pow hr]
  · intro hr
    exact False.elim (hr (Finset.mem_range.mpr (by omega)))

lemma taylor_power_eq_truncatedPowerExpansion (n R : ℕ) (a b : ℝ) (hab : b ≠ a) :
    taylorWithinEval (fun x : ℝ ↦ x ^ n) R (uIcc b a) b a =
      truncatedPowerExpansion n (R + 1) a b := by
  rw [taylor_within_apply, truncatedPowerExpansion]
  apply Finset.sum_congr rfl
  intro r _
  rw [iteratedDerivWithin_pow left_mem_uIcc (uniqueDiffOn_uIcc hab)]
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  simp only [smul_eq_mul, Nat.cast_mul]
  have hfac : (r.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr r.factorial_ne_zero
  field_simp

/-- The remainder retains any common nonnegative bound for the two bases. -/
theorem pow_sub_truncatedPowerExpansion_le (n R : ℕ) (hR : 1 ≤ R)
    {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ M) (hbM : b ≤ M) :
    |a ^ n - truncatedPowerExpansion n R a b| ≤
      (n.choose R : ℝ) * M ^ (n - R) * |a - b| ^ R := by
  by_cases hab : b = a
  · subst b
    rw [truncatedPowerExpansion_self n R hR, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (ha.trans haM) _))
      (pow_nonneg (abs_nonneg _) _)
  have horder : R - 1 + 1 = R := by omega
  obtain ⟨c, hc, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := fun x : ℝ ↦ x ^ n) (n := R - 1) hab (by fun_prop)
  rw [taylor_power_eq_truncatedPowerExpansion n (R - 1) a b hab, horder,
    iteratedDeriv_pow] at he
  have hc0 : 0 ≤ c := (le_min hb ha).trans hc.1.le
  have hcM : c ≤ M := hc.2.le.trans (max_le hbM haM)
  have he' : a ^ n - truncatedPowerExpansion n R a b =
      (n.choose R : ℝ) * c ^ (n - R) * (a - b) ^ R := by
    rw [he, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    have hfac : (R.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr R.factorial_ne_zero
    field_simp
  simp only [he', abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n.choose R)),
    abs_of_nonneg hc0]
  gcongr

end OdlyzkoPoonen
