import OdlyzkoPoonen.FiniteField.PairSums
import OdlyzkoPoonen.FiniteField.InteriorPolynomial
import OdlyzkoPoonen.Probability.WordPrefix

/-!
# Truncating opposite-pair sums

The first `r` positive coefficients of the actual pair-sum polynomial are the
first `r` pair-sum bits, and its constant is zero. Thus products at these
coefficients may use the ordinary shorter interior polynomial.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma coeff_pairSumPolynomial_zero {n : ℕ} (c : Fin (n / 2) → Bool) :
    (pairSumPolynomial c).coeff 0 = 0 := by
  unfold pairSumPolynomial
  rw [coeff_add, (pairedPolynomial_endpoints _ c _).constant,
    (pairedPolynomial_endpoints _ c _).reverse.constant]
  exact CharTwo.add_self_eq_zero _

lemma pairSumPolynomial_prefix {n r : ℕ} (hr : r ≤ n / 2) (c : Fin (n / 2) → Bool)
    {k : ℕ} (hk : k ≤ r) :
    (pairSumPolynomial c).coeff k = (f2InteriorPolynomial (wordPrefix hr c)).coeff k := by
  by_cases hk0 : k = 0
  · rw [hk0, coeff_pairSumPolynomial_zero, coeff_f2InteriorPolynomial_zero]
  · let i : Fin r := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by dsimp [i]; omega
    rw [← hi, coeff_f2InteriorPolynomial]
    change (pairSumPolynomial c).coeff (i.val + 1) =
      bitToF2 (c ⟨i.val, lt_of_lt_of_le i.isLt hr⟩)
    exact coeff_pairSumPolynomial_lower c ⟨i.val, lt_of_lt_of_le i.isLt hr⟩

end OdlyzkoPoonen
