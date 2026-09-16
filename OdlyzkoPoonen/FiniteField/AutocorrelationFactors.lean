import OdlyzkoPoonen.FiniteField.GcdFactors

/-!
# Coprime factors with equal autocorrelation

A common endpoint factor can be cancelled from an autocorrelation identity.
For coprime remaining factors of equal degree, divisibility then forces one
to be the ordinary reverse of the other. No coprimality condition is imposed
on the common factor and its cofactor.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma cancel_common_autocorrelation_factor {d : ℕ} {a b t : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a)
    (h : (a * b) * (a * b).reverse = (a * t) * (a * t).reverse) :
    b * b.reverse = t * t.reverse := by
  apply mul_left_cancel₀ (mul_ne_zero ha.monic.ne_zero ha.reverse.monic.ne_zero)
  calc
    (a * a.reverse) * (b * b.reverse) = (a * b) * (a * b).reverse := by
      rw [reverse_mul_of_domain]
      ring
    _ = (a * t) * (a * t).reverse := h
    _ = (a * a.reverse) * (t * t.reverse) := by
      rw [reverse_mul_of_domain]
      ring

lemma coprime_equal_autocorrelation_reverse {e : ℕ} {b t : (ZMod 2)[X]}
    (hb : HasF2Endpoints e b) (ht : HasF2Endpoints e t)
    (hcop : IsCoprime b t) (h : b * b.reverse = t * t.reverse) : t = b.reverse := by
  have hdiv : b ∣ t * t.reverse := by rw [← h]; exact dvd_mul_right _ _
  have hbdiv : b ∣ t.reverse := hcop.dvd_of_dvd_mul_left hdiv
  have heq : t.reverse = b := eq_of_monic_of_dvd_of_natDegree_le
    hb.monic ht.reverse.monic hbdiv (by rw [ht.reverse.degree, hb.degree])
  simpa only [ht.reverse_reverse] using congrArg Polynomial.reverse heq

end OdlyzkoPoonen
