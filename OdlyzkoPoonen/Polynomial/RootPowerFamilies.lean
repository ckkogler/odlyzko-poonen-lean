import OdlyzkoPoonen.Polynomial.RootFamilies
import OdlyzkoPoonen.Polynomial.RootPowerResultants
import OdlyzkoPoonen.Polynomial.RationalSeparable

/-!
# Explicit root families for integer root-power polynomials

One enumeration of the original roots supplies every powered family. A power
which is injective on the original roots preserves simplicity; distinct
exponents of noncyclotomic conjugates give disjoint families.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma polynomialRootPowers_prod_X_sub_C {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (r : ℕ) :
    polynomialRootPowers (∏ i, (X - C (x i))) r = ∏ i, (X - C (x i ^ r)) := by
  have hm : (∏ i, (X - C (x i))).Monic :=
    monic_prod_of_monic _ _ (fun i _ ↦ monic_X_sub_C _)
  have hr : (∏ i, (X - C (x i))).roots = Finset.univ.val.map x := by
    convert roots_multiset_prod_X_sub_C (Finset.univ.val.map x) using 1
    ·
      simp only [Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod]
  rw [polynomialRootPowers_eq_prod, hm.leadingCoeff, one_pow, map_one, one_mul, hr]
  simp only [Multiset.map_map, Function.comp_def, Finset.prod_eq_multiset_prod]

lemma exists_integer_root_family {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) :
    ∃ x : Fin J.natDegree → ℂ, Function.Injective x ∧
      (∀ i, x i ∈ (J.map (Int.castRingHom ℂ)).roots) ∧
      J.map (Int.castRingHom ℂ) = ∏ i, (X - C (x i)) := by
  have h := exists_injective_complex_root_family (hJ.map (Int.castRingHom ℂ))
    (complex_roots_nodup_of_rational_irreducible hirr)
  rwa [hJ.natDegree_map] at h

lemma root_power_family_factorization {ι : Type*} [Fintype ι]
    {J : ℤ[X]} (x : ι → ℂ)
    (hf : J.map (Int.castRingHom ℂ) = ∏ i, (X - C (x i))) (r : ℕ) :
    (polynomialRootPowers J r).map (Int.castRingHom ℂ) =
      ∏ i, (X - C (x i ^ r)) := by
  rw [polynomialRootPowers_map _ (show Function.Injective (Int.castRingHom ℂ)
    from Int.cast_injective), hf, polynomialRootPowers_prod_X_sub_C]

lemma root_power_family_injective {ι : Type*} {J : ℤ[X]} (x : ι → ℂ)
    (hx : Function.Injective x) (hmem : ∀ i, x i ∈ (J.map (Int.castRingHom ℂ)).roots)
    {r : ℕ} (hr : ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ r = b ^ r → a = b) :
    Function.Injective (fun i ↦ x i ^ r) := by
  intro i j he
  exact hx (hr _ (hmem i) _ (hmem j) he)

lemma root_power_families_disjoint {ι : Type*} {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J) (x : ι → ℂ)
    (hmem : ∀ i, x i ∈ (J.map (Int.castRingHom ℂ)).roots)
    {r s : ℕ} (hrs : r ≠ s) (i j : ι) : x i ^ r ≠ x j ^ s := by
  intro he
  exact hrs (eq_exponents_of_noncyclotomic_complex_root_powers
    hJ hirr hconst hcyc (hmem i) (hmem j) he)

end OdlyzkoPoonen
