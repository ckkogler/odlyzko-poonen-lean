import OdlyzkoPoonen.FiniteField.WordCoefficients
import OdlyzkoPoonen.Probability.OppositeWords
import OdlyzkoPoonen.Probability.FiniteFieldModel

/-!
# Polynomial coordinates from opposite pairs

A word of `n` internal coefficients gives a degree-`n+1` polynomial. Its lower
coefficients are the free bits `u`, and the opposite coefficients are `u+c` in
the field with two elements. The central bit, when present, is a separate
coordinate. The finite-field probability formula follows from the actual word
bijection.
-/

namespace OdlyzkoPoonen
open Polynomial

/-- The actual finite-field polynomial specified by opposite-pair coordinates. -/
noncomputable def pairedPolynomial {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) : (ZMod 2)[X] :=
  f2WordPolynomial (assembleOppositeWord u c z)

lemma pairedPolynomial_endpoints {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) : HasF2Endpoints (n + 1) (pairedPolynomial u c z) :=
  f2WordPolynomial_endpoints _

lemma coeff_pairedPolynomial_lower {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    (pairedPolynomial u c z).coeff (i.val + 1) = bitToF2 (u i) := by
  have h := coeff_f2WordPolynomial_internal (assembleOppositeWord u c z) (lowerWordIndex i)
  simpa only [pairedPolynomial, lowerWordIndex_val, assembleOppositeWord_lower] using h

lemma coeff_pairedPolynomial_upper {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    (pairedPolynomial u c z).coeff (n + 1 - (i.val + 1)) = bitToF2 (u i) + bitToF2 (c i) := by
  have h := coeff_f2WordPolynomial_internal (assembleOppositeWord u c z) (upperWordIndex i)
  have hi : (upperWordIndex i).val + 1 = n + 1 - (i.val + 1) := by
    rw [upperWordIndex_val]
    have := i.isLt
    omega
  simpa only [pairedPolynomial, hi, assembleOppositeWord_upper, bitToF2_xor] using h

lemma coeff_pairedPolynomial_center {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n % 2)) :
    (pairedPolynomial u c z).coeff (n / 2 + 1) = bitToF2 (z i) := by
  have h := coeff_f2WordPolynomial_internal (assembleOppositeWord u c z) (centerWordIndex i)
  simpa only [pairedPolynomial, centerWordIndex_val, assembleOppositeWord_center] using h

lemma coeff_paired_sum_reverse_lower {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    (pairedPolynomial u c z + (pairedPolynomial u c z).reverse).coeff (i.val + 1) =
      bitToF2 (c i) := by
  rw [coeff_add, coeff_reverse, (pairedPolynomial_endpoints u c z).degree,
    revAt_le (show i.val + 1 ≤ n + 1 by have := i.isLt; omega),
    coeff_pairedPolynomial_lower, coeff_pairedPolynomial_upper]
  exact CharTwo.add_cancel_left _ _

lemma coeff_add_reverse_opposite {n k : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (hk : k ≤ n) :
    (p + p.reverse).coeff (n - k) = (p + p.reverse).coeff k := by
  simp only [coeff_add, coeff_reverse, hp.degree, revAt_le hk,
    revAt_le (Nat.sub_le n k), Nat.sub_sub_self hk, add_comm]

lemma coeff_paired_sum_reverse_upper {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    (pairedPolynomial u c z + (pairedPolynomial u c z).reverse).coeff (n + 1 - (i.val + 1)) =
      bitToF2 (c i) := by
  rw [coeff_add_reverse_opposite (pairedPolynomial_endpoints u c z)
    (show i.val + 1 ≤ n + 1 by have := i.isLt; omega), coeff_paired_sum_reverse_lower]

lemma coeff_paired_sum_reverse_center {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n % 2)) :
    (pairedPolynomial u c z + (pairedPolynomial u c z).reverse).coeff (n / 2 + 1) = 0 := by
  have hn : n + 1 - (n / 2 + 1) = n / 2 + 1 := by have := i.isLt; omega
  rw [coeff_add, coeff_reverse, (pairedPolynomial_endpoints u c z).degree,
    revAt_le (show n / 2 + 1 ≤ n + 1 by omega), hn]
  exact CharTwo.add_self_eq_zero _

lemma f2Probability_eq_paired_average (n : ℕ) (E : (ZMod 2)[X] → Prop) :
    f2Probability n E =
      uniformAverage (fun c : Fin (n / 2) → Bool ↦
        uniformAverage (fun z : Fin (n % 2) → Bool ↦
          uniformProbability (fun u : Fin (n / 2) → Bool ↦ E (pairedPolynomial u c z)))) :=
  uniformProbability_oppositeWord n (fun w ↦ E (f2WordPolynomial w))

end OdlyzkoPoonen
