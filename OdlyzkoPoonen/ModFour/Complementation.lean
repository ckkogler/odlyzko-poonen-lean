import OdlyzkoPoonen.ModFour.Parity
import OdlyzkoPoonen.Polynomial.OuterAutocorrelation

/-!
# Complementing the new outer coefficient pair

When the lower opposite pairs remain fixed and both new outer coefficients
are complemented, the change in the half-autocorrelation discrepancy is the
sum modulo two of the four old outer coefficients. This isolates the integer
arithmetic in the fresh-bit formula from the finite-field factor construction.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma halfCoefficientDifference_change {p q p' q' : ℤ[X]} {k : ℕ} {s : ℤ}
    (he : (2 : ℤ) ∣ p.coeff k - q.coeff k)
    (hc : p'.coeff k - q'.coeff k = (p.coeff k - q.coeff k) + 2 * s) :
    halfCoefficientDifference p' q' k - halfCoefficientDifference p q k =
      (s : ZMod 2) := by
  obtain ⟨u, hu⟩ := he
  have hu' : p'.coeff k - q'.coeff k = 2 * (u + s) := by
    rw [hc, hu]
    ring
  simp only [halfCoefficientDifference, hu, hu',
    Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  push_cast
  ring

lemma halfAutocorrelation_change_of_complementation {n k : ℕ} {p q p' q' : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hq : HasBinaryEndpoints n q)
    (hp' : HasBinaryEndpoints n p') (hq' : HasBinaryEndpoints n q')
    (hk0 : 0 < k) (hk : k ≤ n)
    (he : CongruentMod 2 (autocorrelation p) (autocorrelation q))
    (hpl : ∀ i < k, p'.coeff i = p.coeff i)
    (hpr : ∀ i < k, p'.coeff (n - i) = p.coeff (n - i))
    (hql : ∀ i < k, q'.coeff i = q.coeff i)
    (hqr : ∀ i < k, q'.coeff (n - i) = q.coeff (n - i))
    (hpk : p'.coeff k = 1 - p.coeff k)
    (hpnk : p'.coeff (n - k) = 1 - p.coeff (n - k))
    (hqk : q'.coeff k = 1 - q.coeff k)
    (hqnk : q'.coeff (n - k) = 1 - q.coeff (n - k)) :
    halfCoefficientDifference (autocorrelation p') (autocorrelation q') k -
        halfCoefficientDifference (autocorrelation p) (autocorrelation q) k =
      ((p.coeff k + p.coeff (n - k) + q.coeff k + q.coeff (n - k) : ℤ) : ZMod 2) := by
  have hpd := hp'.autocorrelation_outer_difference hp hk0 hk hpl hpr
  have hqd := hq'.autocorrelation_outer_difference hq hk0 hk hql hqr
  rw [hpk, hpnk] at hpd
  rw [hqk, hqnk] at hqd
  have hx := halfCoefficientDifference_change
    ((congruentMod_iff_coeff_dvd _ _ _).mp he k)
    (s := q.coeff k + q.coeff (n - k) - p.coeff k - p.coeff (n - k))
    (p' := autocorrelation p') (q' := autocorrelation q') (by linarith)
  rw [hx]
  push_cast
  simp only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  ring

end OdlyzkoPoonen
