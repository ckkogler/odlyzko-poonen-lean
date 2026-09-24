import OdlyzkoPoonen.Polynomial.RootPowerPrime
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Prime separation for complex roots

The Galois proof takes place in the algebraic splitting field. Its embedding
into `ℂ` contains every complex root, so injectivity of the power map transfers
to the actual complex root set used in Mahler-measure estimates.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma exists_prime_separating_complex_roots_of_log_lt {P : ℚ[X]}
    (hmonic : P.Monic) (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0) {n : ℕ}
    (hgrowth : Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ))
    (hlog : Real.log (2 * (P.natDegree : ℝ) ^ 4) < (n : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 8 * n ∧
      Set.InjOn (fun x : ℂ ↦ x ^ p) (P.rootSet ℂ) := by
  -- The splitting-field algebra and the canonical rational algebra coincide.
  have : Normal ℚ P.SplittingField := by
    convert (Polynomial.SplittingField.instNormal P) using 1 <;> exact Subsingleton.elim _ _
  obtain ⟨p, hp, hnp, hpn, hinj⟩ := exists_prime_separating_root_powers_of_log_lt
    (K := P.SplittingField) hmonic hirr hconst (SplittingField.splits P) hgrowth hlog
  refine ⟨p, hp, hnp, hpn, ?_⟩
  let j : P.SplittingField →ₐ[ℚ] ℂ := SplittingField.lift P (IsAlgClosed.splits _)
  have himage := (SplittingField.splits P).image_rootSet j
  intro z hz w hw he
  rw [← himage] at hz hw
  obtain ⟨a, ha, rfl⟩ := hz
  obtain ⟨b, hb, rfl⟩ := hw
  apply congrArg j
  apply hinj ha hb
  apply j.injective
  change j (a ^ p) = j (b ^ p)
  rw [map_pow, map_pow]
  exact he

lemma exists_prime_separating_integer_polynomial_roots_of_log_lt {J : ℤ[X]}
    (hmonic : J.Monic) (hirr : Irreducible (J.map (Int.castRingHom ℚ)))
    (hconst : J.coeff 0 ≠ 0) {n : ℕ}
    (hgrowth : Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ))
    (hlog : Real.log (2 * (J.natDegree : ℝ) ^ 4) < (n : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 8 * n ∧
      ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ w ∈ (J.map (Int.castRingHom ℂ)).roots, z ^ p = w ^ p → z = w := by
  have hconstQ : (J.map (Int.castRingHom ℚ)).coeff 0 ≠ 0 := by
    simpa only [coeff_map, Int.coe_castRingHom, Int.cast_ne_zero] using hconst
  have hlogQ : Real.log (2 * ((J.map (Int.castRingHom ℚ)).natDegree : ℝ) ^ 4) < n := by
    rwa [natDegree_map_eq_of_injective (Int.cast_injective : Function.Injective
      (Int.castRingHom ℚ))]
  obtain ⟨p, hp, hnp, hpn, hinj⟩ := exists_prime_separating_complex_roots_of_log_lt
    (hmonic.map _) hirr hconstQ hgrowth hlogQ
  have heq : (J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) =
      J.map (Int.castRingHom ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  refine ⟨p, hp, hnp, hpn, ?_⟩
  intro z hz w hw he
  apply hinj ?_ ?_ he
  · change z ∈ ((J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ)).roots.toFinset
    rw [heq]
    exact Multiset.mem_toFinset.mpr hz
  · change w ∈ ((J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ)).roots.toFinset
    rw [heq]
    exact Multiset.mem_toFinset.mpr hw

end OdlyzkoPoonen
