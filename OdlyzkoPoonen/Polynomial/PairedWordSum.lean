import OdlyzkoPoonen.Probability.OppositeWords
import OdlyzkoPoonen.Polynomial.BinaryWords
import OdlyzkoPoonen.Polynomial.Reversal

/-!
# The reciprocal sum in opposite-pair coordinates

The integer polynomial `P + reverse P` is unchanged when an unequal opposite
pair exchanges its two bits. Equal pairs and the middle bit are kept fixed.
The statement concerns the actual integer sum, not only its reduction modulo
two. A separate locality lemma transfers restrictions on pairs to restrictions
on polynomial coefficient positions.
-/

namespace OdlyzkoPoonen
open Polynomial

noncomputable def wordReciprocalSum {m : ℕ} (w : Fin m → Bool) : ℤ[X] :=
  wordPolynomial w + (wordPolynomial w).reverse

lemma coeff_reverse_wordPolynomial_internal {m : ℕ} (w : Fin m → Bool) (i : Fin m) :
    (wordPolynomial w).reverse.coeff (i.val + 1) = bitValue (w i.rev) := by
  rw [coeff_reverse, natDegree_wordPolynomial, revAt_le (by have := i.isLt; omega)]
  have he : m + 1 - (i.val + 1) = i.rev.val + 1 := by
    rw [Fin.val_rev]
    have := i.isLt
    omega
  rw [he, coeff_wordPolynomial_internal]

lemma wordReciprocalSum_coeff_zero {m : ℕ} (w : Fin m → Bool) :
    (wordReciprocalSum w).coeff 0 = 2 := by
  rw [wordReciprocalSum, coeff_add, coeff_wordPolynomial_zero, coeff_zero_reverse,
    (wordPolynomial_endpoints w).monic.leadingCoeff]
  norm_num

lemma wordReciprocalSum_ne_zero {m : ℕ} (w : Fin m → Bool) :
    wordReciprocalSum w ≠ 0 := by
  intro h
  have hc := wordReciprocalSum_coeff_zero w
  rw [h, coeff_zero] at hc
  norm_num at hc

lemma wordReciprocalSum_natDegree {m : ℕ} (w : Fin m → Bool) :
    (wordReciprocalSum w).natDegree = m + 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact (natDegree_add_le _ _).trans (by
      rw [natDegree_wordPolynomial, (wordPolynomial_endpoints w).reverse.degree, max_self])
  · rw [wordReciprocalSum, coeff_add, coeff_wordPolynomial_top,
      (wordPolynomial_endpoints w).reverse.coeff_degree]
    norm_num

lemma assembleOppositeWord_pair_sum_eq {m : ℕ}
    (u v c : Fin (m / 2) → Bool) (z : Fin (m % 2) → Bool)
    (hfixed : ∀ i, c i = false → u i = v i) (i : Fin m) :
    bitValue (assembleOppositeWord u c z i) + bitValue (assembleOppositeWord u c z i.rev) =
      bitValue (assembleOppositeWord v c z i) + bitValue (assembleOppositeWord v c z i.rev) := by
  have hlower (j : Fin (m / 2)) :
      bitValue (assembleOppositeWord u c z (lowerWordIndex j)) +
        bitValue (assembleOppositeWord u c z (upperWordIndex j)) =
      bitValue (assembleOppositeWord v c z (lowerWordIndex j)) +
        bitValue (assembleOppositeWord v c z (upperWordIndex j)) := by
    rw [assembleOppositeWord_lower, assembleOppositeWord_upper,
      assembleOppositeWord_lower, assembleOppositeWord_upper]
    cases hc : c j with
    | false => rw [hfixed j hc]
    | true => cases u j <;> cases v j <;> rfl
  by_cases hl : i.val < m / 2
  · exact hlower ⟨i.val, hl⟩
  by_cases hu : i.rev.val < m / 2
  · have h := hlower ⟨i.rev.val, hu⟩
    have he : upperWordIndex ⟨i.rev.val, hu⟩ = i := Fin.rev_rev i
    simpa only [he, show lowerWordIndex ⟨i.rev.val, hu⟩ = i.rev from rfl, add_comm] using h
  · let j : Fin (m % 2) := ⟨i.val - m / 2, center_index_of_not_outer i hl hu⟩
    have he : centerWordIndex j = i := by
      apply Fin.ext
      change m / 2 + (i.val - m / 2) = i.val
      omega
    rw [← he, centerWordIndex_rev, assembleOppositeWord_center, assembleOppositeWord_center]

lemma wordReciprocalSum_assemble_eq {m : ℕ}
    (u v c : Fin (m / 2) → Bool) (z : Fin (m % 2) → Bool)
    (hfixed : ∀ i, c i = false → u i = v i) :
    wordReciprocalSum (assembleOppositeWord u c z) =
      wordReciprocalSum (assembleOppositeWord v c z) := by
  ext k
  by_cases hk0 : k = 0
  · subst k
    rw [wordReciprocalSum_coeff_zero, wordReciprocalSum_coeff_zero]
  by_cases hkt : k = m + 1
  · subst k
    simp only [wordReciprocalSum, coeff_add, coeff_wordPolynomial_top,
      (wordPolynomial_endpoints _).reverse.coeff_degree]
  by_cases hk : k < m + 1
  · let i : Fin m := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by dsimp [i]; omega
    rw [wordReciprocalSum, wordReciprocalSum, coeff_add, coeff_add, ← hi,
      coeff_wordPolynomial_internal, coeff_reverse_wordPolynomial_internal,
      coeff_wordPolynomial_internal, coeff_reverse_wordPolynomial_internal]
    exact assembleOppositeWord_pair_sum_eq u v c z hfixed i
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [wordReciprocalSum_natDegree]; omega),
      coeff_eq_zero_of_natDegree_lt (by rw [wordReciprocalSum_natDegree]; omega)]

lemma assembleOppositeWord_agree_outside {m : ℕ}
    (u v c : Fin (m / 2) → Bool) (z : Fin (m % 2) → Bool)
    (s : Fin (m / 2) → Prop) (A : Fin m → Prop)
    (hA : ∀ j, s j → A (lowerWordIndex j) ∧ A (upperWordIndex j))
    (hfixed : ∀ j, ¬s j → u j = v j) :
    ∀ i, ¬A i → assembleOppositeWord u c z i = assembleOppositeWord v c z i := by
  intro i hi
  unfold assembleOppositeWord
  split_ifs with hl hu
  · apply hfixed
    intro hs
    exact hi ((hA ⟨i.val, hl⟩ hs).1)
  · have he : upperWordIndex ⟨i.rev.val, hu⟩ = i := Fin.rev_rev i
    have hn : ¬s ⟨i.rev.val, hu⟩ := by
      intro hs
      exact hi (he ▸ (hA ⟨i.rev.val, hu⟩ hs).2)
    rw [hfixed _ hn]
  · rfl

end OdlyzkoPoonen
