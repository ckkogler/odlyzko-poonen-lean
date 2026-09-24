import OdlyzkoPoonen.Polynomial.NoncyclotomicRoots
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Different exponents of complex conjugate roots cannot coincide

The finite root-orbit argument is applied in the rational splitting field and
then transported through its embedding into `ℂ`. The theorem uses the actual
integer polynomial, standard rational irreducibility and absence of a positive
order cyclotomic divisor. No lower bound for a Mahler measure is required.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma eq_exponents_of_noncyclotomic_complex_root_powers {J : ℤ[X]}
    (hmonic : J.Monic) (hirr : Irreducible (J.map (Int.castRingHom ℚ)))
    (hconst : J.coeff 0 ≠ 0) (hcyc : ¬ HasCyclotomicDivisor J) {a b : ℂ}
    (ha : a ∈ (J.map (Int.castRingHom ℂ)).roots)
    (hb : b ∈ (J.map (Int.castRingHom ℂ)).roots) {r s : ℕ}
    (he : a ^ r = b ^ s) : r = s := by
  let P : ℚ[X] := J.map (Int.castRingHom ℚ)
  have : Normal ℚ P.SplittingField := by
    convert (Polynomial.SplittingField.instNormal P) using 1 <;> exact Subsingleton.elim _ _
  have hmap : P.map (algebraMap ℚ ℂ) = J.map (Int.castRingHom ℂ) := by
    dsimp [P]
    rw [Polynomial.map_map]
    congr 1
  have ha' : a ∈ P.rootSet ℂ := by
    change a ∈ (P.map (algebraMap ℚ ℂ)).roots.toFinset
    rw [hmap]
    exact Multiset.mem_toFinset.mpr ha
  have hb' : b ∈ P.rootSet ℂ := by
    change b ∈ (P.map (algebraMap ℚ ℂ)).roots.toFinset
    rw [hmap]
    exact Multiset.mem_toFinset.mpr hb
  let j : P.SplittingField →ₐ[ℚ] ℂ := SplittingField.lift P (IsAlgClosed.splits _)
  have himage := (SplittingField.splits P).image_rootSet j
  rw [← himage] at ha' hb'
  obtain ⟨x, hx, rfl⟩ := ha'
  obtain ⟨y, hy, rfl⟩ := hb'
  apply eq_exponents_of_noncyclotomic_root_powers hmonic hirr hconst hcyc hx hy
  apply j.injective
  change j (x ^ r) = j (y ^ s)
  rw [map_pow, map_pow]
  exact he

end OdlyzkoPoonen
