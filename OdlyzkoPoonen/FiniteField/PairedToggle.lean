import OdlyzkoPoonen.FiniteField.BinaryFamily

/-!
# Toggling an opposite coefficient pair

Adding `X^k + X^(e-k)` over the field with two elements toggles the two opposite
coefficients. For `0 < k` and `2*k < e`, both positions are internal and distinct,
so endpoints and degree are preserved. Reversal commutes with this operation.
The first new coefficient of a product toggles, while earlier coefficients stay
fixed. These facts implement the fresh input bit in polynomial exposure.
-/

namespace OdlyzkoPoonen
open Polynomial

/-- Toggle the two opposite coefficient positions in a degree-`e` polynomial. -/
noncomputable def togglePair (e k : ℕ) (b : (ZMod 2)[X]) : (ZMod 2)[X] :=
  b + (X ^ k + X ^ (e - k))

lemma HasF2Endpoints.togglePair {e k : ℕ} {b : (ZMod 2)[X]}
    (hb : HasF2Endpoints e b) (hk0 : 0 < k) (hk : 2 * k < e) :
    HasF2Endpoints e (togglePair e k b) := by
  have hsmall : (X ^ k + X ^ (e - k) : (ZMod 2)[X]).natDegree < b.natDegree := by
    rw [hb.degree]
    apply lt_of_le_of_lt (natDegree_add_le _ _)
    simp only [natDegree_X_pow]
    exact max_lt (by omega) (by omega)
  refine ⟨hb.monic.add_of_left (degree_lt_degree hsmall),
    (natDegree_add_eq_left_of_natDegree_lt hsmall).trans hb.degree, ?_⟩
  simp [OdlyzkoPoonen.togglePair, hb.constant, coeff_X_pow, show (0 : ℕ) ≠ k by omega,
    show (0 : ℕ) ≠ e - k by omega]

lemma reverse_togglePair {e k : ℕ} {b : (ZMod 2)[X]}
    (hb : HasF2Endpoints e b) (hk0 : 0 < k) (hk : 2 * k < e) :
    (togglePair e k b).reverse = togglePair e k b.reverse := by
  have ht := hb.togglePair hk0 hk
  unfold Polynomial.reverse
  rw [ht.degree, hb.degree]
  simp only [togglePair, reflect_add, reflect_monomial,
    revAt_le (show k ≤ e by omega), revAt_le (Nat.sub_le e k),
    Nat.sub_sub_self (show k ≤ e by omega)]
  rw [add_comm (X ^ (e - k)) (X ^ k)]

lemma coeff_mul_togglePair_before (a b : (ZMod 2)[X]) {e k i : ℕ}
    (hk : 2 * k < e) (hi : i < k) :
    (a * togglePair e k b).coeff i = (a * b).coeff i := by
  simp [togglePair, mul_add, coeff_mul_X_pow',
    show ¬ k ≤ i by omega, show ¬ e - k ≤ i by omega]

lemma coeff_mul_togglePair_at (a b : (ZMod 2)[X]) {e k : ℕ}
    (hk : 2 * k < e) (ha : a.coeff 0 = 1) :
    (a * togglePair e k b).coeff k = (a * b).coeff k + 1 := by
  simp [togglePair, mul_add, coeff_mul_X_pow', ha, show ¬ e - k ≤ k by omega]

lemma coeff_mul_togglePair_opposite {d e k : ℕ} {a b : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (hb : HasF2Endpoints e b)
    (hk0 : 0 < k) (hk : 2 * k < e) :
    (a * togglePair e k b).coeff (d + e - k) = (a * b).coeff (d + e - k) + 1 := by
  have h := coeff_mul_togglePair_at a.reverse b.reverse hk ha.reverse.constant
  rw [← reverse_togglePair hb hk0 hk, ← reverse_mul_of_domain,
    ← reverse_mul_of_domain] at h
  simpa only [coeff_reverse, (ha.mul (hb.togglePair hk0 hk)).degree,
    (ha.mul hb).degree, revAt_le (show k ≤ d + e by omega)] using h

lemma coeff_mul_togglePair_opposite_before {d e k i : ℕ} {a b : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (hb : HasF2Endpoints e b)
    (hk0 : 0 < k) (hk : 2 * k < e) (hi : i < k) :
    (a * togglePair e k b).coeff (d + e - i) = (a * b).coeff (d + e - i) := by
  have h := coeff_mul_togglePair_before a.reverse b.reverse hk hi
  rw [← reverse_togglePair hb hk0 hk, ← reverse_mul_of_domain,
    ← reverse_mul_of_domain] at h
  simpa only [coeff_reverse, (ha.mul (hb.togglePair hk0 hk)).degree,
    (ha.mul hb).degree, revAt_le (show i ≤ d + e by omega)] using h

lemma togglePair_togglePair (e k : ℕ) (b : (ZMod 2)[X]) :
    togglePair e k (togglePair e k b) = b := by
  unfold togglePair
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

lemma togglePair_add_reverse {e k : ℕ} {b : (ZMod 2)[X]}
    (hb : HasF2Endpoints e b) (hk0 : 0 < k) (hk : 2 * k < e) :
    togglePair e k b + (togglePair e k b).reverse = b + b.reverse := by
  rw [reverse_togglePair hb hk0 hk]
  unfold togglePair
  calc
    _ = b + b.reverse + ((X ^ k + X ^ (e - k)) + (X ^ k + X ^ (e - k))) := by abel
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

end OdlyzkoPoonen
