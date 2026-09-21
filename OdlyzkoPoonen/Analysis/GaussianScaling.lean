import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# Scaling homogeneous Gaussian integrals

Dilation separates every homogeneous amplitude into a fixed Gaussian moment
and an explicit half-integer power of the concentration parameter.
-/

namespace OdlyzkoPoonen
open MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem homogeneous_gaussian_integral_scale {h Q : V → ℝ} (j : ℕ)
    {t : ℝ} (ht : 0 < t)
    (hh : ∀ x, h (t • x) = t ^ j * h x)
    (hQ : ∀ x, Q (t • x) = t ^ 2 * Q x) :
    (∫ x : V, h x * Real.exp (-(t ^ 2) * Q x)) =
      (t ^ (Module.finrank ℝ V + j))⁻¹ * ∫ x : V, h x * Real.exp (-Q x) := by
  have he := Measure.integral_comp_smul (volume : Measure V)
    (fun x : V ↦ h x * Real.exp (-Q x)) t
  have he' : t ^ j * (∫ x : V, h x * Real.exp (-(t ^ 2) * Q x)) =
      (t ^ Module.finrank ℝ V)⁻¹ * ∫ x : V, h x * Real.exp (-Q x) := by
    calc
      _ = ∫ x : V, t ^ j * (h x * Real.exp (-(t ^ 2) * Q x)) :=
        (integral_const_mul _ _).symm
      _ = ∫ x : V, h (t • x) * Real.exp (-Q (t • x)) := by
        congr 1
        funext x
        rw [hh, hQ, neg_mul, mul_assoc]
      _ = _ := by
        simpa only [abs_inv, abs_of_pos (pow_pos ht _), smul_eq_mul] using he
  have ht0 := ht.ne'
  rw [pow_add]
  apply (mul_left_cancel₀ (pow_ne_zero j ht0))
  rw [he']
  field_simp

lemma inverse_sqrt_pow_eq_rpow {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    (Real.sqrt x ^ j)⁻¹ = x ^ (-(j : ℝ) / 2) := by
  have he : Real.sqrt x ^ j = x ^ ((j : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
    congr 1
    ring
  rw [he, ← Real.rpow_neg hx]
  congr 1
  ring

theorem homogeneous_gaussian_integral_half_power {h Q : V → ℝ} (j : ℕ)
    (hh : ∀ (t : ℝ), 0 < t → ∀ x, h (t • x) = t ^ j * h x)
    (hQ : ∀ (t : ℝ), 0 < t → ∀ x, Q (t • x) = t ^ 2 * Q x)
    {r : ℝ} (hr : 0 < r) :
    (∫ x : V, h x * Real.exp (-r * Q x)) =
      r ^ (-((Module.finrank ℝ V : ℝ) + j) / 2) *
        ∫ x : V, h x * Real.exp (-Q x) := by
  have hs := Real.sqrt_pos.mpr hr
  have he := homogeneous_gaussian_integral_scale j hs (hh _ hs) (hQ _ hs)
  simpa only [Real.sq_sqrt hr.le, inverse_sqrt_pow_eq_rpow hr.le, Nat.cast_add] using he

end OdlyzkoPoonen
