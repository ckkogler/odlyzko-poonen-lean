import OdlyzkoPoonen.ModFour.Complementation
import OdlyzkoPoonen.FiniteField.PairedToggle

/-!
# The polynomial fresh-bit identity

For `P = s(a*b)` and `Q = s(a*b.reverse)`, toggle the opposite positions `k`
and `e-k` of `b`. The actual half-autocorrelation discrepancy changes by the
coefficient of `(a+a.reverse)*(b+b.reverse)` at `k`, exactly as in the exposure
argument. The endpoint and complementation conditions are derived here from
the finite-field factor construction.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma int_val_add_one_zmod_two (c : ZMod 2) :
    ((c + 1).val : ℤ) = 1 - (c.val : ℤ) := by
  fin_cases c <;> rfl

lemma asymmetry_product_coeff {d e k : ℕ} {a b : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (hb : HasF2Endpoints e b) (hk : k ≤ d + e) :
    ((a + a.reverse) * (b + b.reverse)).coeff k =
      (a * b).coeff k + (a * b).coeff (d + e - k) +
        (a * b.reverse).coeff k + (a * b.reverse).coeff (d + e - k) := by
  have he : (a + a.reverse) * (b + b.reverse) =
      a * b + (a * b).reverse + a * b.reverse + (a * b.reverse).reverse := by
    rw [reverse_mul_of_domain, reverse_mul_of_domain,
      reverse_reverse_of_constant_ne_zero (by rw [hb.constant]; norm_num)]
    ring
  rw [he]
  simp only [coeff_add, coeff_reverse, (ha.mul hb).degree,
    (ha.mul hb.reverse).degree, revAt_le hk]

lemma autocorrelationDiscrepancy_togglePair {d e k : ℕ} {a b : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (hb : HasF2Endpoints e b)
    (hk0 : 0 < k) (hk : 2 * k < e) :
    autocorrelationDiscrepancy a (togglePair e k b) k -
        autocorrelationDiscrepancy a b k =
      ((a + a.reverse) * (b + b.reverse)).coeff k := by
  have hbn : b.coeff 0 ≠ 0 := by rw [hb.constant]; norm_num
  calc
    _ = (((zeroOneLift (a * b)).coeff k + (zeroOneLift (a * b)).coeff (d + e - k) +
          (zeroOneLift (a * b.reverse)).coeff k +
          (zeroOneLift (a * b.reverse)).coeff (d + e - k) : ℤ) : ZMod 2) := by
      unfold autocorrelationDiscrepancy
      rw [reverse_togglePair hb hk0 hk]
      apply halfAutocorrelation_change_of_complementation
        (ha.mul hb).lift (ha.mul hb.reverse).lift
        (ha.mul (hb.togglePair hk0 hk)).lift
        (ha.mul (hb.reverse.togglePair hk0 hk)).lift hk0 (by omega)
        (lifted_factor_autocorrelation_congruent_two a b hbn)
      · intro i hi
        simp only [coeff_zeroOneLift, coeff_mul_togglePair_before a b hk hi]
      · intro i hi
        simp only [coeff_zeroOneLift, coeff_mul_togglePair_opposite_before ha hb hk0 hk hi]
      · intro i hi
        simp only [coeff_zeroOneLift, coeff_mul_togglePair_before a b.reverse hk hi]
      · intro i hi
        simp only [coeff_zeroOneLift,
          coeff_mul_togglePair_opposite_before ha hb.reverse hk0 hk hi]
      · rw [coeff_zeroOneLift, coeff_zeroOneLift, coeff_mul_togglePair_at a b hk ha.constant,
          int_val_add_one_zmod_two]
      · rw [coeff_zeroOneLift, coeff_zeroOneLift, coeff_mul_togglePair_opposite ha hb hk0 hk,
          int_val_add_one_zmod_two]
      · rw [coeff_zeroOneLift, coeff_zeroOneLift,
          coeff_mul_togglePair_at a b.reverse hk ha.constant, int_val_add_one_zmod_two]
      · rw [coeff_zeroOneLift, coeff_zeroOneLift,
          coeff_mul_togglePair_opposite ha hb.reverse hk0 hk, int_val_add_one_zmod_two]
    _ = _ := by
      rw [asymmetry_product_coeff ha hb (by omega)]
      simp only [coeff_zeroOneLift, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]

end OdlyzkoPoonen
