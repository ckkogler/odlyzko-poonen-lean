import OdlyzkoPoonen.FiniteField.BinaryFamily
import OdlyzkoPoonen.FiniteField.WordCoefficients

/-!
# Endpoints of finite-field factors

Every nonzero element of the field with two elements is one, so every nonzero
polynomial over this field is monic. A factorization of an endpoint-one
polynomial therefore has endpoint-one factors. Their degrees add exactly,
and a degree-zero endpoint factor is one. These facts justify the families
used when parametrizing autocorrelation companions by a gcd.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma f2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact (hx rfl).elim
  · rfl

lemma f2_monic_of_ne_zero {p : (ZMod 2)[X]} (hp : p ≠ 0) : p.Monic :=
  f2_eq_one_of_ne_zero (leadingCoeff_ne_zero.mpr hp)

lemma f2_endpoints_of_constant {p : (ZMod 2)[X]} (hp : p.coeff 0 = 1) :
    HasF2Endpoints p.natDegree p := by
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, coeff_zero] at hp
    exact zero_ne_one hp
  exact ⟨f2_monic_of_ne_zero hp0, rfl, hp⟩

lemma HasF2Endpoints.factor_endpoints {n : ℕ} {p a b : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (hab : p = a * b) :
    HasF2Endpoints a.natDegree a ∧ HasF2Endpoints b.natDegree b ∧
      a.natDegree + b.natDegree = n := by
  have hc : a.coeff 0 * b.coeff 0 = 1 := by rw [← mul_coeff_zero, ← hab, hp.constant]
  have hac : a.coeff 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hc
    exact zero_ne_one hc
  have hbc : b.coeff 0 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact zero_ne_one hc
  have ha := f2_endpoints_of_constant (f2_eq_one_of_ne_zero hac)
  have hb := f2_endpoints_of_constant (f2_eq_one_of_ne_zero hbc)
  refine ⟨ha, hb, ?_⟩
  rw [← natDegree_mul ha.monic.ne_zero hb.monic.ne_zero, ← hab, hp.degree]

lemma HasF2Endpoints.reverse_reverse {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) : p.reverse.reverse = p :=
  reverse_reverse_of_constant_ne_zero (by rw [hp.constant]; exact one_ne_zero)

lemma HasF2Endpoints.eq_one_of_degree_zero {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints 0 p) : p = 1 := by
  ext k
  by_cases hk : k = 0
  · rw [hk, hp.constant, coeff_one_zero]
  · rw [hp.coeff_eq_zero_above (by omega), coeff_one, ite_eq_right hk]

lemma HasF2Endpoints.degree_pos_of_nonreciprocal {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (hne : p ≠ p.reverse) : 0 < n := by
  by_contra h
  have hn : n = 0 := by omega
  rw [hn] at hp
  have heq := hp.eq_one_of_degree_zero
  apply hne
  rw [heq]
  simpa only [C_1] using (Polynomial.reverse_C (1 : ZMod 2)).symm

end OdlyzkoPoonen
