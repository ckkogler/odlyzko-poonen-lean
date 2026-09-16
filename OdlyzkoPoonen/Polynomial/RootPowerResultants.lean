import OdlyzkoPoonen.Polynomial.RootPowerRoots
import OdlyzkoPoonen.Polynomial.ResultantDivisibility

/-!
# Root-power resultants and their prime divisibility

A monic root-power polynomial has the same degree and evaluates resultants by
power substitution. This connects integer Frobenius divisibility with the
nonzero cross-resultants of noncyclotomic conjugates.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma polynomialRootPowers_complex_monic {f : ℂ[X]} (hf : f.Monic) (r : ℕ) :
    (polynomialRootPowers f r).Monic := by
  rw [Monic, polynomialRootPowers_leadingCoeff_of_splits f (IsAlgClosed.splits f)]
  simp [hf.leadingCoeff]

lemma polynomialRootPowers_one_complex {f : ℂ[X]} (hf : f.Monic) :
    polynomialRootPowers f 1 = f := by
  rw [polynomialRootPowers_eq_prod]
  simp only [pow_one, hf.leadingCoeff, map_one, one_mul]
  exact ((IsAlgClosed.splits f).eq_prod_roots_of_monic hf).symm

lemma polynomialRootPowers_int_monic {J : ℤ[X]} (hJ : J.Monic) (r : ℕ) :
    (polynomialRootPowers J r).Monic := by
  apply Polynomial.monic_of_injective (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)
  rw [polynomialRootPowers_map _ (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)]
  exact polynomialRootPowers_complex_monic (hJ.map _) r

lemma polynomialRootPowers_int_natDegree {J : ℤ[X]} (hJ : J.Monic) (r : ℕ) :
    (polynomialRootPowers J r).natDegree = J.natDegree := by
  rw [← natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective),
    polynomialRootPowers_map _ (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective),
    polynomialRootPowers_natDegree_of_splits (hJ.map (Int.castRingHom ℂ)).ne_zero
      (IsAlgClosed.splits _) r,
    natDegree_map_eq_of_injective (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)]

lemma resultant_rootPowers_eq_comp_complex {f : ℂ[X]} (hf : f.Monic)
    (g : ℂ[X]) (r : ℕ) :
    resultant (polynomialRootPowers f r) g = resultant f (g.comp (X ^ r)) := by
  rw [resultant_eq_prod_eval _ _ _ le_rfl (IsAlgClosed.splits _),
    resultant_eq_prod_eval _ _ _ le_rfl (IsAlgClosed.splits _),
    (polynomialRootPowers_complex_monic hf r).leadingCoeff, hf.leadingCoeff,
    polynomialRootPowers_complex_roots hf.ne_zero]
  simp [Multiset.map_map, Polynomial.eval_comp]

lemma resultant_rootPowers_eq_comp_int {J : ℤ[X]} (hJ : J.Monic)
    (Q : ℤ[X]) (r : ℕ) :
    resultant (polynomialRootPowers J r) Q = resultant J (Q.comp (X ^ r)) := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  apply hinj
  rw [← resultant_map_injective _ hinj, ← resultant_map_injective _ hinj,
    polynomialRootPowers_map _ hinj, Polynomial.map_comp,
    Polynomial.map_pow, Polynomial.map_X]
  exact resultant_rootPowers_eq_comp_complex (hJ.map _) _ r

lemma prime_pow_degree_dvd_rootPower_resultant {J : ℤ[X]} (hJ : J.Monic)
    {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ^ J.natDegree ∣ resultant (polynomialRootPowers J p) J := by
  rw [resultant_rootPowers_eq_comp_int hJ]
  exact prime_pow_degree_dvd_resultant_comp_X_pow hJ hp

end OdlyzkoPoonen
