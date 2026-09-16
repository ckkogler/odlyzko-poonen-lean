import OdlyzkoPoonen.Polynomial.RootPowerResultants

/-!
# Integer lower bounds for root-power resultants

A nonzero integer multiple of `a` has complex norm at least `a`. The prime
Frobenius congruence therefore supplies a genuine analytic lower bound on each
original-root / prime-power-root cross-resultant.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma nat_le_norm_intCast_of_dvd {a : ℕ} {z : ℤ} (hd : (a : ℤ) ∣ z) (hz : z ≠ 0) :
    (a : ℝ) ≤ ‖(z : ℂ)‖ := by
  have h := Int.natAbs_le_of_dvd_ne_zero hd hz
  have he : ‖(z : ℂ)‖ = (z.natAbs : ℝ) := by
    rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [he]
  exact_mod_cast h

lemma one_le_norm_resultant_int {J Q : ℤ[X]}
    (hc : IsCoprime (J.map (Int.castRingHom ℂ)) (Q.map (Int.castRingHom ℂ))) :
    1 ≤ ‖resultant (J.map (Int.castRingHom ℂ)) (Q.map (Int.castRingHom ℂ))‖ := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hne := resultant_ne_zero _ _ hc
  rw [resultant_map_injective _ hinj] at hne ⊢
  have hz : resultant J Q ≠ 0 := by
    intro hz
    exact hne (by rw [hz, map_zero])
  simpa only [Int.coe_castRingHom, Nat.cast_one] using
    nat_le_norm_intCast_of_dvd (a := 1) (by simp) hz

lemma prime_pow_degree_le_norm_rootPower_resultant {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J) {p : ℕ} (hp : p.Prime) :
    (p : ℝ) ^ J.natDegree ≤
      ‖resultant (polynomialRootPowers (J.map (Int.castRingHom ℂ)) p)
        (J.map (Int.castRingHom ℂ))‖ := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hc := rootPowers_isCoprime_of_distinct_exponents hJ hirr hconst hcyc hp.ne_one
  rw [polynomialRootPowers_one_complex (hJ.map _)] at hc
  have hne := resultant_ne_zero _ _ hc
  rw [← polynomialRootPowers_map _ hinj, resultant_map_injective _ hinj] at hne ⊢
  have hz : resultant (polynomialRootPowers J p) J ≠ 0 := by
    intro hz
    exact hne (by rw [hz, map_zero])
  have hd : ((p ^ J.natDegree : ℕ) : ℤ) ∣ resultant (polynomialRootPowers J p) J := by
    simpa only [Nat.cast_pow] using prime_pow_degree_dvd_rootPower_resultant hJ hp
  simpa only [Int.coe_castRingHom, Nat.cast_pow] using nat_le_norm_intCast_of_dvd hd hz

end OdlyzkoPoonen
