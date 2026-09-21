import OdlyzkoPoonen.Polynomial.CyclotomicFactorization
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Nonconstant monic divisors of cyclotomic products

Every nonconstant monic divisor of a cyclotomic product has a cyclotomic
divisor. This includes products with repeated factors and suffices to separate
the cyclotomic part from any noncyclotomic remainder.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma IsCyclotomicProduct.hasCyclotomicDivisor_of_monic_nonconstant_dvd
    {P Q : ℤ[X]} (hQ : IsCyclotomicProduct Q) (hP : P.Monic)
    (hdeg : 0 < P.natDegree) (hd : P ∣ Q) : HasCyclotomicDivisor P := by
  obtain ⟨J, hJ, hirr, hJP⟩ := exists_monic_rational_irreducible_divisor hP hdeg
  have hJi : Irreducible J :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hJ.isPrimitive).mpr hirr
  have hprime : Prime J := irreducible_iff_prime.mp hJi
  obtain ⟨ks, hks, hQ⟩ := hQ
  have hw : ∀ ls : List ℕ, J ∣ (ls.map (fun k ↦ cyclotomic k ℤ)).prod →
      ∃ k ∈ ls, J ∣ cyclotomic k ℤ := by
    intro ls
    induction ls with
    | nil =>
      intro h
      exact False.elim (hJi.not_isUnit (isUnit_of_dvd_one (by simpa using h)))
    | cons k ls ih =>
      intro h
      simp only [List.map_cons, List.prod_cons] at h
      rcases hprime.dvd_mul.mp h with hk | ht
      · exact ⟨k, by simp, hk⟩
      · obtain ⟨j, hj, hdj⟩ := ih ht
        exact ⟨j, by simp [hj], hdj⟩
  obtain ⟨k, hk, hJk⟩ := hw ks (hQ ▸ hJP.trans hd)
  have he : J = cyclotomic k ℤ := eq_of_monic_of_associated hJ (cyclotomic.monic k ℤ)
    (hJi.associated_of_dvd (cyclotomic.irreducible (hks k hk)) hJk)
  exact ⟨k, hks k hk, he ▸ hJP⟩

lemma not_isCyclotomicProduct_of_monic_nonconstant_noncyclotomic {P : ℤ[X]}
    (hP : P.Monic) (hd : 0 < P.natDegree) (hcyc : ¬ HasCyclotomicDivisor P) :
    ¬ IsCyclotomicProduct P :=
  fun h ↦ hcyc (h.hasCyclotomicDivisor_of_monic_nonconstant_dvd hP hd dvd_rfl)

end OdlyzkoPoonen
