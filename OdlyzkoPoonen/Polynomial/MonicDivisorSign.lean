import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Ring.Associated
import Mathlib.Tactic

/-!
# An integer divisor of a monic polynomial is monic up to sign

The product of leading coefficients is one. Both are therefore integer units,
which are exactly the two signs. This gives a direct normalization without any
assumption on the divisor's degree or constant term.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma monic_or_neg_monic_of_dvd_monic {J P : ℤ[X]} (hP : P.Monic) (hdiv : J ∣ P) :
    J.Monic ∨ (-J).Monic := by
  obtain ⟨Q, hQ⟩ := hdiv
  have he : J.leadingCoeff * Q.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, ← hQ, hP.leadingCoeff]
  have hu : IsUnit J.leadingCoeff := isUnit_iff_dvd_one.mpr ⟨Q.leadingCoeff, he.symm⟩
  rcases Int.isUnit_iff.mp hu with h | h
  · exact Or.inl h
  · right
    change (-J).leadingCoeff = 1
    rw [leadingCoeff_neg, h]
    norm_num

lemma irreducible_map_rat_of_dvd_monic {J P : ℤ[X]} (hP : P.Monic) (hdiv : J ∣ P)
    (hirr : Irreducible J) : Irreducible (J.map (Int.castRingHom ℚ)) := by
  rcases monic_or_neg_monic_of_dvd_monic hP hdiv with hJ | hJ
  · exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hJ.isPrimitive).mp hirr
  · have hi : Irreducible (-J) := (Associated.refl J).neg_right.irreducible hirr
    have hm := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hJ.isPrimitive).mp hi
    have hn := (Associated.refl ((-J).map (Int.castRingHom ℚ))).neg_right.irreducible hm
    simpa only [Polynomial.map_neg, neg_neg] using hn

end OdlyzkoPoonen
