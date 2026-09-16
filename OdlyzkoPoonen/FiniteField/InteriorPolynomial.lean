import OdlyzkoPoonen.FiniteField.WordCoefficients

/-!
# A finite coefficient word with zero constant

This is the reduction of the existing integer interior polynomial. Its bits
occupy positions one through the word length, with all other coefficients zero.
It is useful for truncating the lower coefficients of an opposite-pair sum.
-/

namespace OdlyzkoPoonen
open Polynomial

/-- A Boolean coefficient word in the field with two elements, with zero constant. -/
noncomputable def f2InteriorPolynomial {m : ℕ} (w : Fin m → Bool) : (ZMod 2)[X] :=
  reducePolynomial 2 (interiorPolynomial w)

lemma coeff_f2InteriorPolynomial {m : ℕ} (w : Fin m → Bool) (i : Fin m) :
    (f2InteriorPolynomial w).coeff (i.val + 1) = bitToF2 (w i) := by
  rw [f2InteriorPolynomial, coeff_reducePolynomial, coeff_interiorPolynomial,
    ← bitToF2_eq_int_cast]

lemma coeff_f2InteriorPolynomial_outside {m : ℕ} (w : Fin m → Bool) (k : ℕ)
    (hk : k = 0 ∨ m < k) : (f2InteriorPolynomial w).coeff k = 0 := by
  rw [f2InteriorPolynomial, coeff_reducePolynomial, coeff_interiorPolynomial_outside w k hk,
    Int.cast_zero]

lemma coeff_f2InteriorPolynomial_zero {m : ℕ} (w : Fin m → Bool) :
    (f2InteriorPolynomial w).coeff 0 = 0 :=
  coeff_f2InteriorPolynomial_outside w 0 (Or.inl rfl)

lemma f2InteriorPolynomial_prefix {m : ℕ} {v w : Fin m → Bool} {i : Fin m}
    (h : ∀ j < i, v j = w j) {k : ℕ} (hk : k < i.val + 1) :
    (f2InteriorPolynomial v).coeff k = (f2InteriorPolynomial w).coeff k := by
  by_cases hk0 : k = 0
  · rw [hk0, coeff_f2InteriorPolynomial_zero, coeff_f2InteriorPolynomial_zero]
  · let j : Fin m := ⟨k - 1, by have := i.isLt; omega⟩
    have hj : j.val + 1 = k := by dsimp [j]; omega
    rw [← hj, coeff_f2InteriorPolynomial, coeff_f2InteriorPolynomial]
    congr 1
    apply h j
    change j.val < i.val
    dsimp [j]
    omega

end OdlyzkoPoonen
