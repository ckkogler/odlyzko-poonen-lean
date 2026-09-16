import OdlyzkoPoonen.Polynomial.BinaryDifference
import Mathlib.Algebra.Polynomial.Expand

/-!
# Sparse changes of binary coefficients

After all positions outside the multiples of `q` are fixed, the difference of
two sample polynomials is a polynomial in `X^q`. We use the standard polynomial
`contract` and `expand` operations, prove their identity for this actual
coefficient support, and preserve nonzeroness when the two words differ.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma expand_contract_of_coeff_eq_zero {R : Type*} [CommSemiring R]
    {q : ℕ} (hq : 0 < q) (P : R[X])
    (hs : ∀ k, ¬ q ∣ k → P.coeff k = 0) :
    expand R q (contract q P) = P := by
  ext k
  rw [coeff_expand hq, coeff_contract (ne_of_gt hq)]
  split_ifs with hk
  · rw [Nat.div_mul_cancel hk]
  · exact (hs k hk).symm

lemma coeff_wordPolynomial_sub_eq_zero_of_not_dvd {m q : ℕ}
    (v w : Fin m → Bool)
    (hfixed : ∀ i : Fin m, ¬ q ∣ i.val + 1 → v i = w i)
    {k : ℕ} (hk : ¬ q ∣ k) :
    (wordPolynomial v - wordPolynomial w).coeff k = 0 := by
  by_cases hout : k = 0 ∨ m < k
  · exact coeff_wordPolynomial_sub_outside v w k hout
  · have hkpos : 0 < k := by omega
    have hkle : k ≤ m := by omega
    let i : Fin m := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by dsimp [i]; omega
    rw [coeff_sub, ← hi, coeff_wordPolynomial_internal, coeff_wordPolynomial_internal]
    rw [hfixed i (by simpa only [hi] using hk), sub_self]

lemma sparse_word_difference_expand {m q : ℕ} (hq : 0 < q)
    (v w : Fin m → Bool)
    (hfixed : ∀ i : Fin m, ¬ q ∣ i.val + 1 → v i = w i) :
    expand ℤ q (contract q (wordPolynomial v - wordPolynomial w)) =
      wordPolynomial v - wordPolynomial w := by
  exact expand_contract_of_coeff_eq_zero hq _
    (fun _ hk ↦ coeff_wordPolynomial_sub_eq_zero_of_not_dvd v w hfixed hk)

lemma sparse_word_difference_contract_ne_zero {m q : ℕ} (hq : 0 < q)
    (v w : Fin m → Bool)
    (hfixed : ∀ i : Fin m, ¬ q ∣ i.val + 1 → v i = w i) (hne : v ≠ w) :
    contract q (wordPolynomial v - wordPolynomial w) ≠ 0 := by
  intro hzero
  have heq := sparse_word_difference_expand hq v w hfixed
  rw [hzero, map_zero] at heq
  exact hne (wordPolynomial_injective (sub_eq_zero.mp heq.symm))

end OdlyzkoPoonen
