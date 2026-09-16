import Mathlib.Algebra.Polynomial.Expand
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# Integer polynomial Frobenius congruence

Reduction modulo a prime makes substitution by its power equal to taking that
power. Thus every coefficient of `J(X^p) - J(X)^p` is divisible by `p`.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma comp_X_pow_eq_pow_zmod {p : ℕ} (hp : p.Prime) (f : (ZMod p)[X]) :
    f.comp (X ^ p) = f ^ p := by
  let : Fact p.Prime := ⟨hp⟩
  simpa only [ZMod.frobenius_zmod, Polynomial.map_id,
    Polynomial.expand_eq_comp_X_pow] using Polynomial.map_frobenius_expand p f

lemma prime_C_dvd_comp_X_pow_sub_pow (J : ℤ[X]) {p : ℕ} (hp : p.Prime) :
    C (p : ℤ) ∣ J.comp (X ^ p) - J ^ p := by
  apply (C_dvd_iff_dvd_coeff _ _).mpr
  intro i
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  have hz : (J.comp (X ^ p) - J ^ p).map (Int.castRingHom (ZMod p)) = 0 := by
    simp only [Polynomial.map_sub, Polynomial.map_comp, Polynomial.map_pow,
      Polynomial.map_X, comp_X_pow_eq_pow_zmod hp, sub_self]
  have hc := congrArg (fun f : (ZMod p)[X] ↦ f.coeff i) hz
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero, Int.coe_castRingHom] using hc

end OdlyzkoPoonen
