import OdlyzkoPoonen.Polynomial.PairedWordSum

/-!
# Exact fibers of the integer reciprocal sum

The reciprocal sum determines the unequal-pair mask and the central bit.
On equal pairs it also determines the lower bit. The remaining coordinates
are precisely the independent orientations of unequal pairs.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma wordReciprocalSum_assemble_eq_iff {m : ℕ}
    (u v c d : Fin (m / 2) → Bool) (z t : Fin (m % 2) → Bool) :
    wordReciprocalSum (assembleOppositeWord u c z) =
        wordReciprocalSum (assembleOppositeWord v d t) ↔
      c = d ∧ z = t ∧ ∀ j, c j = false → u j = v j := by
  constructor
  · intro h
    have hpair (j : Fin (m / 2)) :
        bitValue (u j) + bitValue (Bool.xor (u j) (c j)) =
          bitValue (v j) + bitValue (Bool.xor (v j) (d j)) := by
      have hc := congrArg (fun S : ℤ[X] ↦ S.coeff ((lowerWordIndex j).val + 1)) h
      simpa only [wordReciprocalSum, coeff_add, coeff_wordPolynomial_internal,
        coeff_reverse_wordPolynomial_internal, show (lowerWordIndex j).rev = upperWordIndex j from rfl,
        assembleOppositeWord_lower, assembleOppositeWord_upper] using hc
    have hcd : c = d := by
      funext j
      have hj := hpair j
      cases hu : u j <;> cases hv : v j <;> cases hc : c j <;> cases hd : d j <;>
        simp_all [bitValue]
    refine ⟨hcd, ?_, ?_⟩
    · funext j
      have hc := congrArg (fun S : ℤ[X] ↦ S.coeff ((centerWordIndex j).val + 1)) h
      simp only [wordReciprocalSum, coeff_add, coeff_wordPolynomial_internal,
        coeff_reverse_wordPolynomial_internal, centerWordIndex_rev,
        assembleOppositeWord_center] at hc
      cases hz : z j <;> cases ht : t j <;> simp_all [bitValue]
    · intro j hj
      have hh := hpair j
      rw [← hcd, hj] at hh
      cases hu : u j <;> cases hv : v j <;> simp_all [bitValue]
  · rintro ⟨rfl, rfl, hfixed⟩
    exact wordReciprocalSum_assemble_eq u v c z hfixed

end OdlyzkoPoonen
