import OdlyzkoPoonen.Polynomial.SparseWords

/-!
# The coefficient bound after contracting a binary difference

Only the positive multiples of `q` up to `m` contribute to the contracted
polynomial. Its coefficients still have norm at most one. Thus its Mahler
measure is at most `sqrt (m / q)`, with natural division inside the cast. No
assumption that all other positions agree is needed for this upper bound.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

lemma norm_coeff_contract_word_difference_le_one {m q : ℕ} (hq : 0 < q)
    (v w : Fin m → Bool) (k : ℕ) :
    ‖((contract q (wordPolynomial v - wordPolynomial w)).map
      (Int.castRingHom ℂ)).coeff k‖ ≤ 1 := by
  have h := (wordPolynomial_endpoints v).binary.norm_coeff_sub_le_one
    (wordPolynomial_endpoints w).binary (k * q)
  simpa only [coeff_map, coeff_contract (ne_of_gt hq)] using h

lemma support_contract_word_difference_map_subset {m q : ℕ} (hq : 0 < q)
    (v w : Fin m → Bool) :
    ((contract q (wordPolynomial v - wordPolynomial w)).map
      (Int.castRingHom ℂ)).support ⊆ Finset.Icc 1 (m / q) := by
  intro k hk
  have hn : (wordPolynomial v - wordPolynomial w).coeff (k * q) ≠ 0 := by
    intro hz
    exact (mem_support_iff.mp hk) (by
      simp only [coeff_map, coeff_contract (ne_of_gt hq), hz, map_zero])
  have hkpos : 1 ≤ k := by
    by_contra h
    have heq : k = 0 := by omega
    apply hn
    exact coeff_wordPolynomial_sub_outside v w (k * q) (Or.inl (by simp [heq]))
  have hbound : k * q ≤ m := by
    by_contra h
    exact hn (coeff_wordPolynomial_sub_outside v w (k * q) (Or.inr (by omega)))
  exact Finset.mem_Icc.mpr ⟨hkpos, (Nat.le_div_iff_mul_le hq).mpr hbound⟩

lemma mahlerMeasure_contract_word_difference_le {m q : ℕ} (hq : 0 < q)
    (v w : Fin m → Bool) :
    ((contract q (wordPolynomial v - wordPolynomial w)).map
      (Int.castRingHom ℂ)).mahlerMeasure ≤ Real.sqrt ((m / q : ℕ) : ℝ) := by
  classical
  let P := (contract q (wordPolynomial v - wordPolynomial w)).map (Int.castRingHom ℂ)
  have hc (k : ℕ) : ‖P.coeff k‖ ^ 2 ≤ (1 : ℝ) := by
    have h := norm_coeff_contract_word_difference_le_one hq v w k
    change ‖P.coeff k‖ ≤ 1 at h
    nlinarith [norm_nonneg (P.coeff k)]
  have hcard : P.support.card ≤ m / q := by
    have h := Finset.card_le_card (support_contract_word_difference_map_subset hq v w)
    simpa [P, Nat.card_Icc] using h
  calc
    P.mahlerMeasure ≤ Real.sqrt (∑ k ∈ P.support, ‖P.coeff k‖ ^ 2) :=
      mahlerMeasure_le_sqrt_sum_sq_norm_coeff P
    _ ≤ Real.sqrt (∑ _k ∈ P.support, (1 : ℝ)) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum (fun k _ ↦ hc k)
    _ = Real.sqrt (P.support.card : ℝ) := by simp
    _ ≤ Real.sqrt ((m / q : ℕ) : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast hcard

end OdlyzkoPoonen
