import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic

/-!
# A divisor determines the missing low coefficients

Two multiples of a nonzero polynomial that agree in all degrees at or above
the divisor's degree agree everywhere. Their difference would otherwise be a
nonzero multiple of smaller degree. No bound on the low coefficients is used.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma eq_of_dvd_of_high_coefficients_eq {R : Type*} [CommRing R] [IsDomain R]
    {J P Q : R[X]} (hJ : J ≠ 0) (hP : J ∣ P) (hQ : J ∣ Q)
    (hcoeff : ∀ i, J.natDegree ≤ i → P.coeff i = Q.coeff i) : P = Q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_dvd_of_degree_lt (dvd_sub hP hQ)
  rw [degree_eq_natDegree hJ, degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_sub, hcoeff i hi, sub_self]

end OdlyzkoPoonen
