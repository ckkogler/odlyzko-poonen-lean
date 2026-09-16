import OdlyzkoPoonen.Polynomial.CoefficientLocality
import OdlyzkoPoonen.FiniteField.WordCoefficients

/-!
# Outer agreement under finite-field operations

Reversal exchanges the two ends. Multiplication by a fixed endpoint polynomial
preserves the number of agreeing outer coefficients. Zero-one lifting preserves
each coefficient equality. These are the locality steps for discrepancy bits.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma AgreeOnOuter.reverse {n k : ℕ} {p q : (ZMod 2)[X]}
    (h : AgreeOnOuter n k p q) (hp : HasF2Endpoints n p) (hq : HasF2Endpoints n q)
    (hk : k ≤ n) : AgreeOnOuter n k p.reverse q.reverse := by
  constructor
  · intro i hi
    simpa only [coeff_reverse, hp.degree, hq.degree, revAt_le (hi.trans hk)] using h.2 i hi
  · intro i hi
    simpa only [coeff_reverse, hp.degree, hq.degree, revAt_le (Nat.sub_le n i),
      Nat.sub_sub_self (hi.trans hk)] using h.1 i hi

lemma AgreeOnOuter.mul_left {d e k : ℕ} {a b b' : (ZMod 2)[X]}
    (h : AgreeOnOuter e k b b') (ha : HasF2Endpoints d a)
    (hb : HasF2Endpoints e b) (hb' : HasF2Endpoints e b') (hk : k ≤ e) :
    AgreeOnOuter (d + e) k (a * b) (a * b') := by
  constructor
  · intro i hi
    exact coeff_mul_right_eq_of_prefix a (fun j hj ↦ h.1 j (hj.trans hi))
  · intro i hi
    have hr := h.reverse hb hb' hk
    have he := coeff_mul_right_eq_of_prefix a.reverse (fun j hj ↦ hr.1 j (hj.trans hi))
    rw [← reverse_mul_of_domain, ← reverse_mul_of_domain] at he
    simpa only [coeff_reverse, (ha.mul hb).degree, (ha.mul hb').degree,
      revAt_le (show i ≤ d + e by omega)] using he

lemma AgreeOnOuter.zeroOneLift {n k : ℕ} {p q : (ZMod 2)[X]}
    (h : AgreeOnOuter n k p q) : AgreeOnOuter n k (zeroOneLift p) (zeroOneLift q) := by
  constructor
  · intro i hi
    rw [coeff_zeroOneLift, coeff_zeroOneLift, h.1 i hi]
  · intro i hi
    rw [coeff_zeroOneLift, coeff_zeroOneLift, h.2 i hi]

end OdlyzkoPoonen
