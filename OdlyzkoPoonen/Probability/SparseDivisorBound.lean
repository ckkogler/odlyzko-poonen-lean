import OdlyzkoPoonen.Polynomial.RationalSeparable
import OdlyzkoPoonen.Polynomial.SparseDivisorUniqueness
import OdlyzkoPoonen.Arithmetic.SparsePositions
import OdlyzkoPoonen.Probability.SelectedCoordinates
import OdlyzkoPoonen.Probability.BinaryModel

/-!
# Divisibility probabilities from sparse uniqueness

The conditional uniqueness lemma determines all bits in positive positions
divisible by `q`, after the other bits are fixed. Their exact number is `m/q`,
and each fair-bit atom has mass `1/2`. The probability bound follows from the
proved finite conditioning law, with deterministic endpoints unchanged.
The Mahler and root-separation hypotheses here are intermediate arithmetic
conditions, not assumptions permitted in the final noncyclotomic estimate.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma uniformProbability_bool_eq (b : Bool) :
    uniformProbability (fun a : Bool ↦ a = b) = (1 / 2 : ℝ) := by
  letI : DecidablePred (fun a : Bool ↦ a = b) := fun _ ↦ Classical.propDecidable _
  have hfilter : Finset.univ.filter (fun a : Bool ↦ a = b) = {b} := by
    ext a
    simp
  rw [uniformProbability, hfilter]
  norm_num

lemma binaryProbability_divisible_le_sparse {m q : ℕ} (hq : 0 < q) {J : ℤ[X]}
    (hJ : J.Monic) (hsimple : (J.map (Int.castRingHom ℂ)).roots.Nodup)
    (hsep : ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ w ∈ (J.map (Int.castRingHom ℂ)).roots, z ^ q = w ^ q → z = w)
    (hlarge : Real.sqrt ((m / q : ℕ) : ℝ) <
      (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ q) :
    binaryProbability m (fun P ↦ J ∣ P) ≤ (1 / 2 : ℝ) ^ (m / q) := by
  letI : DecidablePred (fun i : Fin m ↦ q ∣ i.val + 1) :=
    fun _ ↦ Classical.propDecidable _
  calc
    _ ≤ ∏ _i : {i : Fin m // q ∣ i.val + 1}, (1 / 2 : ℝ) := by
      apply uniformProbability_selected_coordinates_le
        (fun i : Fin m ↦ q ∣ i.val + 1) (fun w ↦ J ∣ wordPolynomial w)
        (fun _ (a : Bool) ↦ a) (fun _ ↦ (1 / 2 : ℝ))
      · intro _ _; norm_num
      · intro _ _ b; exact (uniformProbability_bool_eq b).le
      · intro v w hv hw hfixed i _
        exact congrFun (word_eq_of_sparse_divisibility hq hJ hsimple hsep hlarge
          v w hv hw hfixed) i
    _ = _ := by
      rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, card_sparse_internal_positions]

lemma binaryProbability_rational_irreducible_divisible_le_sparse {m q : ℕ}
    (hq : 0 < q) {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ)))
    (hsep : ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ w ∈ (J.map (Int.castRingHom ℂ)).roots, z ^ q = w ^ q → z = w)
    (hlarge : Real.sqrt ((m / q : ℕ) : ℝ) <
      (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ q) :
    binaryProbability m (fun P ↦ J ∣ P) ≤ (1 / 2 : ℝ) ^ (m / q) := by
  exact binaryProbability_divisible_le_sparse hq hJ
    (complex_roots_nodup_of_rational_irreducible hirr) hsep hlarge

end OdlyzkoPoonen
