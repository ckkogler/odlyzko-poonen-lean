import OdlyzkoPoonen.Probability.OppositePairConcentration
import OdlyzkoPoonen.Polynomial.PairedWordSumFibers

/-!
# Pair-mask concentration for the actual binary word

The mask of unequal opposite pairs is uniformly distributed. Equality of the
integer reciprocal sums forces equality of these masks, so the concentration
event is determined by that sum. The finite prime-union estimate therefore
applies directly before conditioning the binary sample.
-/

namespace OdlyzkoPoonen

def oppositePairMask {m : ℕ} (w : Fin m → Bool) (j : Fin (m / 2)) : Bool :=
  Bool.xor (w (lowerWordIndex j)) (w (upperWordIndex j))

lemma oppositePairMask_assemble {m : ℕ} (u c : Fin (m / 2) → Bool)
    (z : Fin (m % 2) → Bool) : oppositePairMask (assembleOppositeWord u c z) = c := by
  funext j
  simp only [oppositePairMask, assembleOppositeWord_lower, assembleOppositeWord_upper]
  cases u j <;> cases c j <;> rfl

lemma oppositePairMask_eq_of_reciprocalSum_eq {m : ℕ} {v w : Fin m → Bool}
    (h : wordReciprocalSum v = wordReciprocalSum w) : oppositePairMask v = oppositePairMask w := by
  have hv : assembleOppositeWord (fun j ↦ v (lowerWordIndex j)) (oppositePairMask v)
      (fun j ↦ v (centerWordIndex j)) = v := assembleOppositeWord_recover v
  have hw : assembleOppositeWord (fun j ↦ w (lowerWordIndex j)) (oppositePairMask w)
      (fun j ↦ w (centerWordIndex j)) = w := assembleOppositeWord_recover w
  have hh := (wordReciprocalSum_assemble_eq_iff
    (fun j ↦ v (lowerWordIndex j)) (fun j ↦ w (lowerWordIndex j))
    (oppositePairMask v) (oppositePairMask w)
    (fun j ↦ v (centerWordIndex j)) (fun j ↦ w (centerWordIndex j))).mp
    (by rw [hv, hw]; exact h)
  exact hh.1

lemma uniformProbability_oppositePairMask (m : ℕ) (E : (Fin (m / 2) → Bool) → Prop) :
    uniformProbability (fun w : Fin m → Bool ↦ E (oppositePairMask w)) = uniformProbability E := by
  classical
  rw [uniformProbability_oppositeWord]
  simp_rw [oppositePairMask_assemble, uniformProbability_eq_average_indicator,
    uniformAverage_const]

theorem word_opposite_prime_pairs_concentration {n : ℕ} {T : ℝ}
    (hT : 2 ≤ T) (hn : 8 * T ≤ (n : ℝ)) :
    uniformProbability (fun w : Fin (n - 1) → Bool ↦
      HasSparseOppositePrimePairs n T (oppositePairMask w)) ≤
        2 * T * Real.exp (-(n : ℝ) / (128 * T)) := by
  rw [uniformProbability_oppositePairMask]
  exact opposite_prime_pairs_concentration hT hn

lemma sparseOppositePrimePairs_iff_of_reciprocalSum_eq {n : ℕ} {T : ℝ}
    {v w : Fin (n - 1) → Bool} (h : wordReciprocalSum v = wordReciprocalSum w) :
    HasSparseOppositePrimePairs n T (oppositePairMask v) ↔
      HasSparseOppositePrimePairs n T (oppositePairMask w) := by
  rw [oppositePairMask_eq_of_reciprocalSum_eq h]

end OdlyzkoPoonen
