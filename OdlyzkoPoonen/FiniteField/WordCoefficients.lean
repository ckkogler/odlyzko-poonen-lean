import OdlyzkoPoonen.FiniteField.BinaryFamily
import OdlyzkoPoonen.FiniteField.Bits

/-!
# Coefficients and reversal of finite-field word polynomials

Each internal bit is the corresponding coefficient in the field with two
elements. Reversing the word reverses the actual polynomial, with its fixed
endpoint coefficients and degree preserved.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma HasF2Endpoints.coeff_degree {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) : p.coeff n = 1 := by
  rw [← hp.degree]
  exact hp.monic

lemma HasF2Endpoints.coeff_eq_zero_above {n k : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (hk : n < k) : p.coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [hp.degree]; exact hk)

lemma coeff_f2WordPolynomial_internal {n : ℕ} (w : Fin n → Bool) (i : Fin n) :
    (f2WordPolynomial w).coeff (i.val + 1) = bitToF2 (w i) := by
  rw [f2WordPolynomial, coeff_reducePolynomial, coeff_wordPolynomial_internal,
    ← bitToF2_eq_int_cast]

lemma f2WordPolynomial_ext {n : ℕ} {p q : (ZMod 2)[X]}
    (hp : HasF2Endpoints (n + 1) p) (hq : HasF2Endpoints (n + 1) q)
    (h : ∀ i : Fin n, p.coeff (i.val + 1) = q.coeff (i.val + 1)) : p = q := by
  ext k
  by_cases hk0 : k = 0
  · rw [hk0, hp.constant, hq.constant]
  by_cases hkt : k = n + 1
  · subst k
    rw [← hp.degree]
    change p.leadingCoeff = q.coeff p.natDegree
    rw [hp.monic.leadingCoeff, hp.degree, ← hq.degree]
    exact hq.monic.symm
  by_cases hk : k < n + 1
  · let i : Fin n := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by dsimp [i]; omega
    simpa only [hi] using h i
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [hp.degree]; omega),
      coeff_eq_zero_of_natDegree_lt (by rw [hq.degree]; omega)]

lemma reverse_f2WordPolynomial {n : ℕ} (w : Fin n → Bool) :
    (f2WordPolynomial w).reverse = f2WordPolynomial (fun i ↦ w i.rev) := by
  apply f2WordPolynomial_ext (f2WordPolynomial_endpoints w).reverse
    (f2WordPolynomial_endpoints _)
  intro i
  rw [coeff_reverse, (f2WordPolynomial_endpoints w).degree,
    revAt_le (show i.val + 1 ≤ n + 1 by have := i.isLt; omega)]
  have hi : n + 1 - (i.val + 1) = i.rev.val + 1 := by
    rw [Fin.val_rev]
    have := i.isLt
    omega
  rw [hi, coeff_f2WordPolynomial_internal, coeff_f2WordPolynomial_internal]

end OdlyzkoPoonen
