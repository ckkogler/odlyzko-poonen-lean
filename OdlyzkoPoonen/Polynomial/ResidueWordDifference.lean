import OdlyzkoPoonen.Polynomial.SparseWords
import OdlyzkoPoonen.Polynomial.ContractedBinaryDifference

/-!
# Contracting a difference supported in one residue class

Multiplication by a power of `X` moves an arbitrary residue class to zero.
The shifted difference is then an actual polynomial in `X^q`. Its contracted
coefficients remain bounded by one. The coarse degree bound here is uniform in
the residue and sufficient for the uniform Mahler argument.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

lemma expand_contract_shifted_of_residue_support {q a : ℕ} (hq : 0 < q)
    (ha : a < q) (P : ℤ[X]) (hs : ∀ k, k % q ≠ a → P.coeff k = 0) :
    expand ℤ q (contract q (X ^ (q - a) * P)) = X ^ (q - a) * P := by
  apply expand_contract_of_coeff_eq_zero hq
  intro k hk
  rw [coeff_X_pow_mul']
  split_ifs with h
  · apply hs
    intro he
    have hd : (k - (q - a) + (q - a)) % q = 0 := by
      calc
        _ = (a + (q - a)) % q := by
          rw [Nat.add_mod (k - (q - a)) (q - a) q, he,
            Nat.add_mod a (q - a) q, Nat.mod_eq_of_lt ha]
        _ = 0 := by rw [show a + (q - a) = q by omega]; exact Nat.mod_self _
    apply hk
    exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.sub_add_cancel h] using hd)
  · rfl

lemma coeff_wordPolynomial_sub_eq_zero_of_residue {m q a : ℕ}
    (v w : Fin m → Bool)
    (hfixed : ∀ i : Fin m, (i.val + 1) % q ≠ a → v i = w i)
    {k : ℕ} (hk : k % q ≠ a) :
    (wordPolynomial v - wordPolynomial w).coeff k = 0 := by
  by_cases hout : k = 0 ∨ m < k
  · exact coeff_wordPolynomial_sub_outside v w k hout
  · let i : Fin m := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by dsimp [i]; omega
    rw [coeff_sub, ← hi, coeff_wordPolynomial_internal, coeff_wordPolynomial_internal]
    rw [hfixed i (by simpa only [hi] using hk), sub_self]

lemma residue_word_difference_expand {m q a : ℕ} (hq : 0 < q) (ha : a < q)
    (v w : Fin m → Bool)
    (hfixed : ∀ i : Fin m, (i.val + 1) % q ≠ a → v i = w i) :
    expand ℤ q (contract q (X ^ (q - a) * (wordPolynomial v - wordPolynomial w))) =
      X ^ (q - a) * (wordPolynomial v - wordPolynomial w) :=
  expand_contract_shifted_of_residue_support hq ha _
    (fun _ hk ↦ coeff_wordPolynomial_sub_eq_zero_of_residue v w hfixed hk)

lemma norm_coeff_contract_shifted_word_difference_le_one {m q a : ℕ}
    (hq : 0 < q) (v w : Fin m → Bool) (k : ℕ) :
    ‖((contract q (X ^ a * (wordPolynomial v - wordPolynomial w))).map
      (Int.castRingHom ℂ)).coeff k‖ ≤ 1 := by
  rw [coeff_map, coeff_contract hq.ne', coeff_X_pow_mul']
  split_ifs
  · simpa only [coeff_map] using
      (wordPolynomial_endpoints v).binary.norm_coeff_sub_le_one
        (wordPolynomial_endpoints w).binary (k * q - a)
  · simp

lemma support_contract_shifted_word_difference_subset {m q a : ℕ}
    (hq : 0 < q) (ha : a ≤ q) (v w : Fin m → Bool) :
    ((contract q (X ^ a * (wordPolynomial v - wordPolynomial w))).map
      (Int.castRingHom ℂ)).support ⊆ Finset.range (m + q + 1) := by
  intro k hk
  apply Finset.mem_range.mpr
  by_contra h
  have hkm : m + q < k := by omega
  have hqk : k ≤ k * q := Nat.le_mul_of_pos_right k hq
  have hle : a ≤ k * q := by omega
  have hout : m < k * q - a := by omega
  have hz := coeff_wordPolynomial_sub_outside v w (k * q - a) (Or.inr hout)
  apply (mem_support_iff.mp hk)
  simp only [coeff_map, coeff_contract hq.ne', coeff_X_pow_mul', ite_eq_left hle, hz,
    map_zero]

lemma mahlerMeasure_contract_shifted_word_difference_le {m q a : ℕ}
    (hq : 0 < q) (ha : a ≤ q) (v w : Fin m → Bool) :
    ((contract q (X ^ a * (wordPolynomial v - wordPolynomial w))).map
      (Int.castRingHom ℂ)).mahlerMeasure ≤ Real.sqrt ((m + q + 1 : ℕ) : ℝ) := by
  classical
  let P := (contract q (X ^ a * (wordPolynomial v - wordPolynomial w))).map
    (Int.castRingHom ℂ)
  have hc (k : ℕ) : ‖P.coeff k‖ ^ 2 ≤ (1 : ℝ) := by
    have h := norm_coeff_contract_shifted_word_difference_le_one (a := a) hq v w k
    change ‖P.coeff k‖ ≤ 1 at h
    nlinarith [norm_nonneg (P.coeff k)]
  have hcard : P.support.card ≤ m + q + 1 := by
    simpa [P] using Finset.card_le_card
      (support_contract_shifted_word_difference_subset hq ha v w)
  calc
    P.mahlerMeasure ≤ Real.sqrt (∑ k ∈ P.support, ‖P.coeff k‖ ^ 2) :=
      mahlerMeasure_le_sqrt_sum_sq_norm_coeff P
    _ ≤ Real.sqrt (∑ _k ∈ P.support, (1 : ℝ)) :=
      Real.sqrt_le_sqrt (Finset.sum_le_sum (fun k _ ↦ hc k))
    _ = Real.sqrt (P.support.card : ℝ) := by simp
    _ ≤ _ := Real.sqrt_le_sqrt (by exact_mod_cast hcard)

end OdlyzkoPoonen
