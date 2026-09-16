import OdlyzkoPoonen.FiniteField.PairedPolynomial

/-!
# The opposite-pair sum polynomial

In opposite-pair coordinates, the full polynomial `b+b.reverse` depends only on
the pair-sum word. Both its endpoint coefficients vanish, and its central
coefficient vanishes when a center exists. This proves the meaning of fixing
`c` in the exposure argument, including the unused center.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma paired_sum_reverse_eq {n : ℕ} (u u' c : Fin (n / 2) → Bool)
    (z z' : Fin (n % 2) → Bool) :
    pairedPolynomial u c z + (pairedPolynomial u c z).reverse =
      pairedPolynomial u' c z' + (pairedPolynomial u' c z').reverse := by
  have hp := pairedPolynomial_endpoints u c z
  have hq := pairedPolynomial_endpoints u' c z'
  ext k
  by_cases hk0 : k = 0
  · rw [hk0]
    simp only [coeff_add, hp.constant, hp.reverse.constant, hq.constant, hq.reverse.constant]
  by_cases hkt : k = n + 1
  · rw [hkt]
    simp only [coeff_add, hp.coeff_degree, hp.reverse.coeff_degree,
      hq.coeff_degree, hq.reverse.coeff_degree]
  by_cases hk : k < n + 1
  · by_cases hl : k - 1 < n / 2
    · let i : Fin (n / 2) := ⟨k - 1, hl⟩
      have hi : i.val + 1 = k := by dsimp [i]; omega
      rw [← hi, coeff_paired_sum_reverse_lower u c z i,
        coeff_paired_sum_reverse_lower u' c z' i]
    · by_cases hu : n - k < n / 2
      · let i : Fin (n / 2) := ⟨n - k, hu⟩
        have hi : n + 1 - (i.val + 1) = k := by dsimp [i]; omega
        rw [← hi, coeff_paired_sum_reverse_upper u c z i,
          coeff_paired_sum_reverse_upper u' c z' i]
      · have hi : k = n / 2 + 1 := by omega
        let j : Fin (n % 2) := ⟨0, by omega⟩
        rw [hi, coeff_paired_sum_reverse_center u c z j,
          coeff_paired_sum_reverse_center u' c z' j]
  · have hkn : n + 1 < k := by omega
    simp only [coeff_add, hp.coeff_eq_zero_above hkn, hp.reverse.coeff_eq_zero_above hkn,
      hq.coeff_eq_zero_above hkn, hq.reverse.coeff_eq_zero_above hkn]

/-- The full polynomial determined by the opposite-pair sums. -/
noncomputable def pairSumPolynomial {n : ℕ} (c : Fin (n / 2) → Bool) : (ZMod 2)[X] :=
  pairedPolynomial (fun _ ↦ false) c (fun _ ↦ false) +
    (pairedPolynomial (fun _ ↦ false) c (fun _ ↦ false)).reverse

lemma paired_sum_reverse_eq_pairSumPolynomial {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) :
    pairedPolynomial u c z + (pairedPolynomial u c z).reverse = pairSumPolynomial c :=
  paired_sum_reverse_eq u (fun _ ↦ false) c z (fun _ ↦ false)

lemma coeff_pairSumPolynomial_lower {n : ℕ} (c : Fin (n / 2) → Bool) (i : Fin (n / 2)) :
    (pairSumPolynomial c).coeff (i.val + 1) = bitToF2 (c i) :=
  coeff_paired_sum_reverse_lower (fun _ ↦ false) c (fun _ ↦ false) i

lemma pairSumPolynomial_injective {n : ℕ} : Function.Injective (@pairSumPolynomial n) := by
  intro c d h
  funext i
  apply bitF2Equiv.injective
  change bitToF2 (c i) = bitToF2 (d i)
  have hi := congrArg (fun p : (ZMod 2)[X] ↦ p.coeff (i.val + 1)) h
  simpa only [coeff_pairSumPolynomial_lower] using hi

end OdlyzkoPoonen
