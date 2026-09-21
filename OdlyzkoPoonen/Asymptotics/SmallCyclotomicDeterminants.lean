import OdlyzkoPoonen.Asymptotics.MonicDeterminantLeadingTerm
import OdlyzkoPoonen.Polynomial.SmallCyclotomicRemainders

/-!
# Exact Gram determinants for the small cyclotomic events

The finite remainder tables reduce the determinants to exact real arithmetic.
These are kernel-checked finite identities, independent of numerical integration.
-/

namespace OdlyzkoPoonen
open Polynomial Matrix
open scoped BigOperators Classical

lemma monicDivisorGramMatrix_det_eq_remainder_table {f : ℤ[X]} {q d : ℕ}
    (hd : f.natDegree = d) (r : Fin q → ℤ[X])
    (hr : ∀ i : Fin q, (X : ℤ[X]) ^ i.val %ₘ f = r i) :
    (monicDivisorGramMatrix f q).det =
      (latticeGramMatrix (fun i : Fin q ↦ fun j : Fin d ↦ (r i).coeff j.val)).det := by
  subst d
  congr 1
  ext i j
  simp only [monicDivisorGramMatrix, latticeGramMatrix, latticeCoordinateMatrix,
    Matrix.mul_apply, Matrix.transpose_apply, powerRemainderCoordinates,
    remainderCoordinates_apply, hr]

lemma cyclotomic_three_gram_determinant :
    (monicDivisorGramMatrix (cyclotomic 3 ℤ) 3).det = 3 := by
  rw [monicDivisorGramMatrix_det_eq_remainder_table
    (show (cyclotomic 3 ℤ).natDegree = 2 by rw [natDegree_cyclotomic]; decide)
    (fun j ↦ ![1, X, -X - 1] j) cyclotomic_three_power_remainders]
  norm_num [latticeGramMatrix, latticeCoordinateMatrix, Matrix.det_fin_two,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    coeff_sub, coeff_neg, coeff_one, coeff_X]

lemma cyclotomic_four_gram_determinant :
    (monicDivisorGramMatrix (cyclotomic 4 ℤ) 4).det = 4 := by
  rw [monicDivisorGramMatrix_det_eq_remainder_table
    (show (cyclotomic 4 ℤ).natDegree = 2 by rw [natDegree_cyclotomic]; decide)
    (fun j ↦ ![1, X, -1, -X] j) cyclotomic_four_power_remainders]
  norm_num [latticeGramMatrix, latticeCoordinateMatrix, Matrix.det_fin_two,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    coeff_sub, coeff_neg, coeff_one, coeff_X, coeff_add, coeff_mul, coeff_X_pow]

lemma cyclotomic_six_gram_determinant :
    (monicDivisorGramMatrix (cyclotomic 6 ℤ) 6).det = 12 := by
  rw [monicDivisorGramMatrix_det_eq_remainder_table
    (show (cyclotomic 6 ℤ).natDegree = 2 by rw [natDegree_cyclotomic]; decide)
    (fun j ↦ ![1, X, X - 1, -1, -X, 1 - X] j) cyclotomic_six_power_remainders]
  norm_num [latticeGramMatrix, latticeCoordinateMatrix, Matrix.det_fin_two,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    coeff_sub, coeff_neg, coeff_one, coeff_X, coeff_add, coeff_mul, coeff_X_pow]

lemma cyclotomic_two_three_gram_determinant :
    (monicDivisorGramMatrix (cyclotomic 2 ℤ * cyclotomic 3 ℤ) 6).det = 72 := by
  rw [monicDivisorGramMatrix_det_eq_remainder_table
    (show (cyclotomic 2 ℤ * cyclotomic 3 ℤ).natDegree = 3 by rw [(cyclotomic.monic 2 ℤ).natDegree_mul (cyclotomic.monic 3 ℤ), natDegree_cyclotomic, natDegree_cyclotomic]; decide)
    (fun j ↦ ![1, X, X ^ 2, -2 * X ^ 2 - 2 * X - 1, 2 * X ^ 2 + 3 * X + 2, -X ^ 2 - 2 * X - 2] j) cyclotomic_two_three_power_remainders]
  norm_num [latticeGramMatrix, latticeCoordinateMatrix, Matrix.det_fin_three,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    coeff_sub, coeff_neg, coeff_one, coeff_X, coeff_add, coeff_mul, coeff_X_pow]

lemma cyclotomic_two_four_gram_determinant :
    (monicDivisorGramMatrix (cyclotomic 2 ℤ * cyclotomic 4 ℤ) 4).det = 4 := by
  rw [monicDivisorGramMatrix_det_eq_remainder_table
    (show (cyclotomic 2 ℤ * cyclotomic 4 ℤ).natDegree = 3 by rw [(cyclotomic.monic 2 ℤ).natDegree_mul (cyclotomic.monic 4 ℤ), natDegree_cyclotomic, natDegree_cyclotomic]; decide)
    (fun j ↦ ![1, X, X ^ 2, -X ^ 2 - X - 1] j) cyclotomic_two_four_power_remainders]
  norm_num [latticeGramMatrix, latticeCoordinateMatrix, Matrix.det_fin_three,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    coeff_sub, coeff_neg, coeff_one, coeff_X, coeff_add, coeff_mul, coeff_X_pow]

lemma cyclotomic_two_six_gram_determinant :
    (monicDivisorGramMatrix (cyclotomic 2 ℤ * cyclotomic 6 ℤ) 6).det = 8 := by
  rw [monicDivisorGramMatrix_det_eq_remainder_table
    (show (cyclotomic 2 ℤ * cyclotomic 6 ℤ).natDegree = 3 by rw [(cyclotomic.monic 2 ℤ).natDegree_mul (cyclotomic.monic 6 ℤ), natDegree_cyclotomic, natDegree_cyclotomic]; decide)
    (fun j ↦ ![1, X, X ^ 2, -1, -X, -X ^ 2] j) cyclotomic_two_six_power_remainders]
  norm_num [latticeGramMatrix, latticeCoordinateMatrix, Matrix.det_fin_three,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
    coeff_sub, coeff_neg, coeff_one, coeff_X, coeff_add, coeff_mul, coeff_X_pow]

end OdlyzkoPoonen
