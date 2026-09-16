import OdlyzkoPoonen.FiniteField.FactorEndpoints
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Gcd factors of equal-degree endpoint polynomials

Dividing two endpoint-one polynomials by their gcd gives coprime cofactors.
Every factor has endpoint one, and the degree sums are exact. This supplies the
algebraic data for the autocorrelation companion parametrization.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma exists_coprime_endpoint_factors {n : ℕ} {F G : (ZMod 2)[X]}
    (hF : HasF2Endpoints n F) (hG : HasF2Endpoints n G) :
    ∃ a b t : (ZMod 2)[X],
      F = a * b ∧ G = a * t ∧
      HasF2Endpoints a.natDegree a ∧ HasF2Endpoints b.natDegree b ∧
      HasF2Endpoints t.natDegree t ∧ IsCoprime b t ∧
      a.natDegree + b.natDegree = n ∧ a.natDegree + t.natDegree = n := by
  let a := GCDMonoid.gcd F G
  let b := F / a
  let t := G / a
  have ha : a ≠ 0 := gcd_ne_zero_of_left hF.monic.ne_zero
  have hFb : F = a * b := (EuclideanDomain.mul_div_cancel' ha (gcd_dvd_left F G)).symm
  have hGt : G = a * t := (EuclideanDomain.mul_div_cancel' ha (gcd_dvd_right F G)).symm
  obtain ⟨hA, hB, hdegF⟩ := hF.factor_endpoints hFb
  obtain ⟨_, hT, hdegG⟩ := hG.factor_endpoints hGt
  exact ⟨a, b, t, hFb, hGt, hA, hB, hT,
    isCoprime_div_gcd_div_gcd hG.monic.ne_zero, hdegF, hdegG⟩

end OdlyzkoPoonen
