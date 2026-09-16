import OdlyzkoPoonen.Analysis.PolynomialRootPowers
import OdlyzkoPoonen.Polynomial.ComplexConjugatePowers

/-!
# Roots and coprimality of the root-power polynomials

The resultant construction has exactly the powered root multiset. For a monic
irreducible noncyclotomic integer polynomial with nonzero constant, different
natural exponents give coprime complex root-power polynomials. This justifies
nonzero cross-resultants in the determinant argument.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma polynomialRootPowers_complex_ne_zero {P : ℂ[X]} (hP : P ≠ 0) (r : ℕ) :
    polynomialRootPowers P r ≠ 0 := by
  intro hz
  have hl := polynomialRootPowers_leadingCoeff_of_splits P (IsAlgClosed.splits P) r
  rw [hz, leadingCoeff_zero] at hl
  exact (pow_ne_zero r (leadingCoeff_ne_zero.mpr hP)) hl.symm

lemma polynomialRootPowers_complex_roots {P : ℂ[X]} (hP : P ≠ 0) (r : ℕ) :
    (polynomialRootPowers P r).roots = P.roots.map (fun a ↦ a ^ r) := by
  rw [polynomialRootPowers_eq_prod, roots_C_mul _ (pow_ne_zero r (leadingCoeff_ne_zero.mpr hP))]
  have he : P.roots.map (fun a ↦ X - C (a ^ r)) =
      (P.roots.map (fun a ↦ a ^ r)).map (fun a ↦ X - C a) := by
    rw [Multiset.map_map]
    rfl
  rw [he, roots_multiset_prod_X_sub_C]

lemma rootPowers_isCoprime_of_distinct_exponents {J : ℤ[X]} (hmonic : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J) {r s : ℕ} (hrs : r ≠ s) :
    IsCoprime (polynomialRootPowers (J.map (Int.castRingHom ℂ)) r)
      (polynomialRootPowers (J.map (Int.castRingHom ℂ)) s) := by
  have hJ : J.map (Int.castRingHom ℂ) ≠ 0 := (hmonic.map _).ne_zero
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
  intro z
  by_contra! h
  have hz₁ : z ∈ (polynomialRootPowers (J.map (Int.castRingHom ℂ)) r).roots := by
    apply (mem_roots (polynomialRootPowers_complex_ne_zero hJ r)).mpr
    exact h.1
  have hz₂ : z ∈ (polynomialRootPowers (J.map (Int.castRingHom ℂ)) s).roots := by
    apply (mem_roots (polynomialRootPowers_complex_ne_zero hJ s)).mpr
    exact h.2
  rw [polynomialRootPowers_complex_roots hJ] at hz₁ hz₂
  obtain ⟨a, ha, he₁⟩ := Multiset.mem_map.mp hz₁
  obtain ⟨b, hb, he₂⟩ := Multiset.mem_map.mp hz₂
  exact hrs (eq_exponents_of_noncyclotomic_complex_root_powers
    hmonic hirr hconst hcyc ha hb (he₁.trans he₂.symm))

end OdlyzkoPoonen
