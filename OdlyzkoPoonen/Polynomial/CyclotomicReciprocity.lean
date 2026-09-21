import OdlyzkoPoonen.Polynomial.CyclotomicFactorization
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Reciprocity of cyclotomic factors in binary endpoint polynomials

Cyclotomic polynomials of order greater than one are reciprocal: the inverse
of a primitive root is again primitive. A cyclotomic product dividing a binary
endpoint polynomial has no order-one factor and is therefore reciprocal,
including multiplicities and the empty product.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma cyclotomic_reverse_eq {k : ℕ} (hk : 1 < k) :
    (cyclotomic k ℤ).reverse = cyclotomic k ℤ := by
  have hk0 : 0 < k := by omega
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / k)
  have hζ : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk0.ne'
  let : Invertible (ζ⁻¹) := invertibleOfNonzero (inv_ne_zero (hζ.ne_zero hk0.ne'))
  have he : (cyclotomic k ℤ).eval₂ (Int.castRingHom ℂ) (ζ⁻¹) = 0 := by
    rw [eval₂_eq_eval_map, map_cyclotomic_int]
    exact hζ.inv.isRoot_cyclotomic hk0
  have hr := (eval₂_reverse_eq_zero_iff (Int.castRingHom ℂ) (ζ⁻¹) (cyclotomic k ℤ)).mpr he
  have hd : cyclotomic k ℤ ∣ (cyclotomic k ℤ).reverse := by
    conv_lhs => rw [cyclotomic_eq_minpoly hζ hk0]
    apply minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hk0)
    simpa [aeval_def, invOf_eq_inv] using hr
  have hconst : (cyclotomic k ℤ).coeff 0 ≠ 0 := by
    rw [cyclotomic_coeff_zero ℤ hk]
    norm_num
  have hm : (cyclotomic k ℤ).reverse.Monic := by
    change (cyclotomic k ℤ).reverse.leadingCoeff = 1
    rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero hconst, cyclotomic_coeff_zero ℤ hk]
  exact eq_of_monic_of_dvd_of_natDegree_le (cyclotomic.monic k ℤ) hm hd
    (reverse_natDegree_le _)

lemma IsCyclotomicProduct.reverse_eq_of_not_one_dvd {Q : ℤ[X]}
    (hQ : IsCyclotomicProduct Q) (hnot : ¬ cyclotomic 1 ℤ ∣ Q) : Q.reverse = Q := by
  obtain ⟨ks, hks, rfl⟩ := hQ
  induction ks with
  | nil => simp only [List.map_nil, List.prod_nil, reverse, natDegree_one, reflect_one, pow_zero]
  | cons k ks ih =>
    simp only [List.map_cons, List.prod_cons] at hnot ⊢
    have hk : 1 < k := by
      have hp := hks k (by simp)
      have hne : k ≠ 1 := by
        intro h
        subst k
        exact hnot (dvd_mul_right _ _)
      omega
    have htail : ¬ cyclotomic 1 ℤ ∣ (ks.map (fun j ↦ cyclotomic j ℤ)).prod := by
      intro h
      exact hnot (dvd_mul_of_dvd_right h _)
    rw [reverse_mul_of_domain, cyclotomic_reverse_eq hk,
      ih (fun j hj ↦ hks j (by simp [hj])) htail]

lemma HasBinaryEndpoints.cyclotomic_product_reciprocal {n : ℕ} {P Q : ℤ[X]}
    (hp : HasBinaryEndpoints n P) (hQ : IsCyclotomicProduct Q) (hd : Q ∣ P) :
    Q.reverse = Q :=
  hQ.reverse_eq_of_not_one_dvd (fun h ↦ hp.not_cyclotomic_one_dvd (h.trans hd))

end OdlyzkoPoonen
