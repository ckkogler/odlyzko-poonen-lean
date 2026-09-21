import OdlyzkoPoonen.Polynomial.ResiduePolynomial
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Integral coordinates for divisibility by a monic polynomial

The coefficients of the monic remainder give canonical integral coordinates.
The first powers of `X` give the standard basis. When the divisor divides
`X^k-1`, the vectors are periodic, and a divisor of the geometric sum has
zero total vector over one period.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

/-- Coefficient coordinates of the remainder modulo a monic divisor. -/
noncomputable def remainderCoordinates (f : ℤ[X]) :
    ℤ[X] →ₗ[ℤ] (Fin f.natDegree → ℤ) :=
  LinearMap.pi (fun i ↦ (Polynomial.lcoeff ℤ i.val).comp (modByMonicHom f))

lemma remainderCoordinates_apply (f p : ℤ[X]) (i : Fin f.natDegree) :
    remainderCoordinates f p i = (p %ₘ f).coeff i.val := rfl

/-- The remainder vector of a single power of `X`. -/
noncomputable def powerRemainderCoordinates (f : ℤ[X]) (j : ℕ) :
    Fin f.natDegree → ℤ := remainderCoordinates f (X ^ j)

theorem remainderCoordinates_eq_zero_iff {f p : ℤ[X]} (hf : f.Monic) :
    remainderCoordinates f p = 0 ↔ f ∣ p := by
  rw [← modByMonic_eq_zero_iff_dvd hf]
  constructor
  · intro h
    ext i
    by_cases hi : i < f.natDegree
    · exact congrFun h ⟨i, hi⟩
    · have hdeg := degree_modByMonic_lt p hf
      rw [degree_eq_natDegree hf.ne_zero, degree_lt_iff_coeff_zero] at hdeg
      simpa only [coeff_zero] using hdeg i (by omega)
  · intro h
    ext i
    simp [remainderCoordinates_apply, h]

lemma powerRemainderCoordinates_basis {f : ℤ[X]} (hf : f.Monic)
    (i j : Fin f.natDegree) :
    powerRemainderCoordinates f i.val j = if j = i then 1 else 0 := by
  have he : (X ^ i.val : ℤ[X]) %ₘ f = X ^ i.val := by
    apply (modByMonic_eq_self_iff hf).mpr
    rw [degree_X_pow, degree_eq_natDegree hf.ne_zero]
    exact_mod_cast i.isLt
  simp [powerRemainderCoordinates, remainderCoordinates_apply, he, coeff_X_pow, Fin.ext_iff]

lemma powerRemainderCoordinates_periodic {f : ℤ[X]} {k : ℕ}
    (hf : f.Monic) (hperiod : f ∣ X ^ k - 1) (j : ℕ) :
    powerRemainderCoordinates f (j + k) = powerRemainderCoordinates f j := by
  have hd : f ∣ (X ^ (j + k) : ℤ[X]) - X ^ j := by
    have he : (X ^ (j + k) : ℤ[X]) - X ^ j = X ^ j * (X ^ k - 1) := by
      rw [pow_add]
      ring
    rw [he]
    exact dvd_mul_of_dvd_right hperiod _
  ext i
  exact congrArg (fun p : ℤ[X] ↦ p.coeff i.val) (modByMonic_eq_of_dvd_sub hf hd)

lemma powerRemainderCoordinates_sum_eq_zero {f : ℤ[X]} {k : ℕ}
    (hf : f.Monic) (hgeom : f ∣ ∑ j ∈ Finset.range k, (X : ℤ[X]) ^ j) :
    ∑ j ∈ Finset.range k, powerRemainderCoordinates f j = 0 := by
  simpa only [powerRemainderCoordinates, map_sum] using
    (remainderCoordinates_eq_zero_iff hf).mpr hgeom

lemma wordPolynomial_remainderCoordinates {m : ℕ} (f : ℤ[X]) (w : Fin m → Bool) :
    remainderCoordinates f (wordPolynomial w) =
      powerRemainderCoordinates f 0 +
        (∑ i, bitValue (w i) • powerRemainderCoordinates f (i.val + 1)) +
        powerRemainderCoordinates f (m + 1) := by
  simp only [wordPolynomial, interiorPolynomial, map_add, map_sum, C_mul',
    map_smul, powerRemainderCoordinates, pow_zero]

/-- Divisibility is a finite integer linear system in the internal bits. -/
theorem dvd_wordPolynomial_iff_remainderCoordinates_eq_zero {m : ℕ} {f : ℤ[X]}
    (hf : f.Monic) (w : Fin m → Bool) :
    f ∣ wordPolynomial w ↔
      powerRemainderCoordinates f 0 +
        (∑ i, bitValue (w i) • powerRemainderCoordinates f (i.val + 1)) +
        powerRemainderCoordinates f (m + 1) = 0 := by
  rw [← remainderCoordinates_eq_zero_iff hf, wordPolynomial_remainderCoordinates]

end OdlyzkoPoonen
