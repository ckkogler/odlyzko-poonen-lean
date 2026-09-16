import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

/-!
# Simple complex roots of an irreducible rational polynomial

Characteristic zero gives separability over the rationals, and coefficient
extension preserves it. The identity of the two integer-to-complex maps is
proved explicitly so the resulting root multiset is the canonical one used
in the Mahler and sparse-word estimates.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma complex_roots_nodup_of_rational_irreducible {J : ℤ[X]}
    (hJ : Irreducible (J.map (Int.castRingHom ℚ))) :
    (J.map (Int.castRingHom ℂ)).roots.Nodup := by
  have heq : (J.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) =
      J.map (Int.castRingHom ℂ) := by
    rw [Polynomial.map_map]
    congr 1
  rw [← heq]
  exact nodup_roots hJ.separable.map

end OdlyzkoPoonen
