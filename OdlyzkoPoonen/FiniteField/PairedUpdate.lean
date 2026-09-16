import OdlyzkoPoonen.FiniteField.PairedPolynomial
import OdlyzkoPoonen.FiniteField.PairedToggle

/-!
# A fresh lower bit is the actual polynomial toggle

At fixed opposite-pair sums, complementing a lower bit complements its upper
partner too. The central coefficient is unchanged. The following identity
connects the word coordinates used for counting to the polynomial operation
in the discrepancy calculation; it includes both word parities.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma pairedPolynomial_update {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    pairedPolynomial (Function.update u i (!(u i))) c z =
      togglePair (n + 1) (i.val + 1) (pairedPolynomial u c z) := by
  classical
  have hi := i.isLt
  have ht : 2 * (i.val + 1) < n + 1 := by omega
  apply f2WordPolynomial_ext (pairedPolynomial_endpoints _ c z)
    ((pairedPolynomial_endpoints u c z).togglePair (by omega) ht)
  intro j
  have hj := j.isLt
  by_cases hl : j.val < n / 2
  · let l : Fin (n / 2) := ⟨j.val, hl⟩
    change (pairedPolynomial _ c z).coeff (l.val + 1) = _
    rw [coeff_pairedPolynomial_lower]
    change _ = (togglePair (n + 1) (i.val + 1) (pairedPolynomial u c z)).coeff (l.val + 1)
    simp only [togglePair, coeff_add, coeff_pairedPolynomial_lower, coeff_X_pow]
    have hupper : l.val + 1 ≠ n + 1 - (i.val + 1) := by have := l.isLt; omega
    by_cases hli : l = i
    · rw [hli] at hupper ⊢
      simp only [Function.update_self, bitToF2_not, ite_true,
        ite_eq_right hupper, add_zero]
    · have hlow : l.val + 1 ≠ i.val + 1 := by
        intro h
        exact hli (Fin.ext (by omega))
      simp only [Function.update_of_ne hli, ite_eq_right hlow, ite_eq_right hupper,
        add_zero]
  · by_cases hu : n - (j.val + 1) < n / 2
    · let l : Fin (n / 2) := ⟨n - (j.val + 1), hu⟩
      have heq : j.val + 1 = n + 1 - (l.val + 1) := by dsimp [l]; omega
      rw [heq, coeff_pairedPolynomial_upper]
      simp only [togglePair, coeff_add, coeff_pairedPolynomial_upper, coeff_X_pow]
      have hlower : n + 1 - (l.val + 1) ≠ i.val + 1 := by have := l.isLt; omega
      by_cases hli : l = i
      · rw [hli] at hlower ⊢
        simp only [Function.update_self, bitToF2_not, ite_eq_right hlower,
          ite_true, zero_add]
        rw [add_right_comm]
      · have hupper : n + 1 - (l.val + 1) ≠ n + 1 - (i.val + 1) := by
          intro h
          have := l.isLt
          exact hli (Fin.ext (by omega))
        simp only [Function.update_of_ne hli, ite_eq_right hlower, ite_eq_right hupper,
          add_zero]
    · have heq : j.val + 1 = n / 2 + 1 := by omega
      let l : Fin (n % 2) := ⟨0, by omega⟩
      rw [heq, coeff_pairedPolynomial_center _ c z l]
      simp only [togglePair, coeff_add, coeff_pairedPolynomial_center u c z l, coeff_X_pow]
      have hlower : n / 2 + 1 ≠ i.val + 1 := by omega
      have hupper : n / 2 + 1 ≠ n + 1 - (i.val + 1) := by have := l.isLt; omega
      simp only [ite_eq_right hlower, ite_eq_right hupper, add_zero]

end OdlyzkoPoonen
