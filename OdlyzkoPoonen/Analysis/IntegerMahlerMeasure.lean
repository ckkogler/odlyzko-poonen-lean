import Mathlib.NumberTheory.MahlerMeasure
import OdlyzkoPoonen.Polynomial.CyclotomicDivisors

/-!
# Integer Mahler measure and noncyclotomic factors

These comparisons use the standard complex Mahler measure of the coefficient
map of an integer polynomial. Multiplicativity and the integer lower bound
make it monotone under divisibility of a nonzero polynomial. Kronecker's
proved theorem gives strict positivity of its logarithm outside the factors
`X` and the cyclotomic polynomials. The positivity is qualitative; it does not
supply the uniform quantitative lower bound needed in the fixed-factor estimate.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma one_le_norm_leadingCoeff_int_map {P : ℤ[X]} (hP : P ≠ 0) :
    1 ≤ ‖(P.map (Int.castRingHom ℂ)).leadingCoeff‖ := by
  rw [leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int, eq_intCast]
  norm_cast
  exact Int.one_le_abs (leadingCoeff_ne_zero.mpr hP)

lemma int_mahlerMeasure_le_of_dvd {J P : ℤ[X]} (hd : J ∣ P) (hP : P ≠ 0) :
    (J.map (Int.castRingHom ℂ)).mahlerMeasure ≤
      (P.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨R, rfl⟩ := hd
  have hR : R ≠ 0 := right_ne_zero_of_mul hP
  rw [Polynomial.map_mul, mahlerMeasure_mul]
  exact le_mul_of_one_le_right (mahlerMeasure_nonneg _)
    (one_le_mahlerMeasure_of_ne_zero hR)

lemma one_lt_mahlerMeasure_of_no_cyclotomic {J : ℤ[X]}
    (hdegree : 0 < J.natDegree) (hX : ¬ X ∣ J)
    (hcyclotomic : ¬ HasCyclotomicDivisor J) :
    1 < (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hJ : J ≠ 0 := by intro h; simp [h] at hdegree
  have hle := one_le_mahlerMeasure_of_ne_zero hJ
  apply lt_of_le_of_ne hle
  intro heq
  exact hcyclotomic (cyclotomic_dvd_of_mahlerMeasure_eq_one heq.symm hX
    (ne_of_gt (natDegree_pos_iff_degree_pos.mp hdegree)))

lemma log_mahlerMeasure_pos_of_no_cyclotomic {J : ℤ[X]}
    (hdegree : 0 < J.natDegree) (hX : ¬ X ∣ J)
    (hcyclotomic : ¬ HasCyclotomicDivisor J) :
    0 < Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  exact Real.log_pos (one_lt_mahlerMeasure_of_no_cyclotomic hdegree hX hcyclotomic)

end OdlyzkoPoonen
