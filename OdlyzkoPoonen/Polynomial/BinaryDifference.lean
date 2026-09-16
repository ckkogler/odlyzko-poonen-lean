import Mathlib.Analysis.Polynomial.MahlerMeasure
import OdlyzkoPoonen.Polynomial.BinaryWords

/-!
# Differences of endpoint-fixed binary words

A difference has coefficients in `{-1,0,1}`. The deterministic constant and
leading coefficients cancel, so only the actual internal positions remain.
Landau's proved coefficient inequality therefore bounds the Mahler measure by
`sqrt m` for words with `m` free bits, including the empty-word case.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

lemma IsBinary.norm_coeff_sub_le_one {P Q : ℤ[X]} (hP : IsBinary P)
    (hQ : IsBinary Q) (k : ℕ) :
    ‖((P - Q).map (Int.castRingHom ℂ)).coeff k‖ ≤ 1 := by
  rcases hP k with hp | hp <;> rcases hQ k with hq | hq <;>
    simp [coeff_map, coeff_sub, hp, hq]

lemma coeff_wordPolynomial_sub_outside {m : ℕ} (v w : Fin m → Bool) (k : ℕ)
    (hk : k = 0 ∨ m < k) : (wordPolynomial v - wordPolynomial w).coeff k = 0 := by
  rw [coeff_sub]
  rcases hk with rfl | hk
  · simp only [coeff_wordPolynomial_zero, sub_self]
  · by_cases ht : k = m + 1
    · subst k
      simp only [coeff_wordPolynomial_top, sub_self]
    · rw [coeff_wordPolynomial_above v (by omega),
        coeff_wordPolynomial_above w (by omega), sub_self]

lemma support_wordPolynomial_sub_map_subset {m : ℕ} (v w : Fin m → Bool) :
    ((wordPolynomial v - wordPolynomial w).map (Int.castRingHom ℂ)).support ⊆
      Finset.Icc 1 m := by
  intro k hk
  by_contra h
  have hout : k = 0 ∨ m < k := by simp only [Finset.mem_Icc] at h; omega
  have hz := coeff_wordPolynomial_sub_outside v w k hout
  exact (mem_support_iff.mp hk) (by simp only [coeff_map, hz, map_zero])

lemma mahlerMeasure_wordPolynomial_sub_le {m : ℕ} (v w : Fin m → Bool) :
    ((wordPolynomial v - wordPolynomial w).map (Int.castRingHom ℂ)).mahlerMeasure ≤
      Real.sqrt (m : ℝ) := by
  classical
  let P := (wordPolynomial v - wordPolynomial w).map (Int.castRingHom ℂ)
  have hc (k : ℕ) : ‖P.coeff k‖ ^ 2 ≤ (1 : ℝ) := by
    have h := (wordPolynomial_endpoints v).binary.norm_coeff_sub_le_one
      (wordPolynomial_endpoints w).binary k
    change ‖P.coeff k‖ ≤ 1 at h
    nlinarith [norm_nonneg (P.coeff k)]
  have hcard : P.support.card ≤ m := by
    have h := Finset.card_le_card (support_wordPolynomial_sub_map_subset v w)
    simpa [P, Nat.card_Icc] using h
  calc
    P.mahlerMeasure ≤ Real.sqrt (∑ k ∈ P.support, ‖P.coeff k‖ ^ 2) :=
      mahlerMeasure_le_sqrt_sum_sq_norm_coeff P
    _ ≤ Real.sqrt (∑ _k ∈ P.support, (1 : ℝ)) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum (fun k _ ↦ hc k)
    _ = Real.sqrt (P.support.card : ℝ) := by simp
    _ ≤ Real.sqrt (m : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast hcard

end OdlyzkoPoonen
