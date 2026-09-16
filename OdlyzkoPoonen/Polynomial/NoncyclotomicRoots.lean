import OdlyzkoPoonen.Polynomial.ConjugatePowers
import OdlyzkoPoonen.Polynomial.CyclotomicDivisors

/-!
# Roots of irreducible noncyclotomic polynomials have infinite order

A torsion root has a positive order and its rational minimal polynomial is the
corresponding cyclotomic polynomial. Rational irreducibility identifies the
original polynomial with that minimal polynomial. The existing integer/rational
divisibility equivalence then excludes torsion without any analytic estimate.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma root_pow_ne_one_of_no_cyclotomic {K : Type*} [Field K] [CharZero K]
    {J : ℤ[X]} (hmonic : J.Monic) (hirr : Irreducible (J.map (Int.castRingHom ℚ)))
    (hcyc : ¬ HasCyclotomicDivisor J) {a : K}
    (ha : a ∈ (J.map (Int.castRingHom ℚ)).rootSet K) {r : ℕ} (hr : 0 < r) :
    a ^ r ≠ 1 := by
  intro he
  have hfinite : IsOfFinOrder a := isOfFinOrder_iff_pow_eq_one.mpr ⟨r, hr, he⟩
  have horder := hfinite.orderOf_pos
  have hmin : J.map (Int.castRingHom ℚ) = minpoly ℚ a :=
    minpoly.eq_of_irreducible_of_monic hirr (aeval_eq_zero_of_mem_rootSet ha) (hmonic.map _)
  have heq : cyclotomic (orderOf a) ℚ = J.map (Int.castRingHom ℚ) :=
    (cyclotomic_eq_minpoly_rat (IsPrimitiveRoot.orderOf a) horder).trans hmin.symm
  apply hcyc
  refine ⟨orderOf a, horder, (cyclotomic_dvd_iff_rational _ _).mpr ?_⟩
  rw [heq]

lemma eq_exponents_of_noncyclotomic_root_powers {K : Type*} [Field K] [CharZero K]
    [Normal ℚ K] {J : ℤ[X]} (hmonic : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J) {a b : K}
    (ha : a ∈ (J.map (Int.castRingHom ℚ)).rootSet K)
    (hb : b ∈ (J.map (Int.castRingHom ℚ)).rootSet K) {r s : ℕ}
    (he : a ^ r = b ^ s) : r = s := by
  apply eq_exponents_of_conjugate_root_powers (hmonic.map _) hirr ?_ ha hb
    (fun k hk ↦ root_pow_ne_one_of_no_cyclotomic hmonic hirr hcyc ha hk) he
  simpa only [coeff_map, Int.coe_castRingHom, Int.cast_ne_zero] using hconst

end OdlyzkoPoonen
