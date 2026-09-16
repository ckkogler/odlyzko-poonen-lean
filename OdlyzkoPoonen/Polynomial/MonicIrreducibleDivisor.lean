import OdlyzkoPoonen.Polynomial.MonicDivisorSign
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# A nonconstant monic integer polynomial has a monic irreducible divisor

Choose an integer irreducible factor, normalize its sign, and apply Gauss's
lemma. The result is an actual integer divisor with standard rational
irreducibility, ready for the uniform fixed-factor probability bound.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma exists_monic_rational_irreducible_divisor {P : ℤ[X]} (hP : P.Monic)
    (hdegree : 0 < P.natDegree) :
    ∃ J : ℤ[X], J.Monic ∧ Irreducible (J.map (Int.castRingHom ℚ)) ∧ J ∣ P := by
  have hunit : ¬ IsUnit P := by
    intro h
    have he := hP.isUnit_iff.mp h
    simp [he] at hdegree
  obtain ⟨J, hirr, hdiv⟩ := WfDvdMonoid.exists_irreducible_factor hunit hP.ne_zero
  rcases monic_or_neg_monic_of_dvd_monic hP hdiv with hJ | hJ
  · exact ⟨J, hJ, irreducible_map_rat_of_dvd_monic hP hdiv hirr, hdiv⟩
  · have hneg : Irreducible (-J) := (Associated.refl J).neg_right.irreducible hirr
    exact ⟨-J, hJ, irreducible_map_rat_of_dvd_monic hP hdiv.neg_left hneg, hdiv.neg_left⟩

end OdlyzkoPoonen
