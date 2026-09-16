import OdlyzkoPoonen.Probability.OppositeIndices
import OdlyzkoPoonen.Probability.UniformAverage

/-!
# Coordinates given by opposite pairs

The explicit coordinates of a word are its opposite-pair sums, central bit
(if present), and lower bits. The upper bit is recovered as lower xor pair sum.
This is a bijection of the actual finite word spaces, not an independence
assumption. Coordinates are ordered so that fixing pair sums and the center
leaves the lower word as the innermost probability space.
-/

namespace OdlyzkoPoonen

/-- Reconstruct a word from its lower bits, opposite-pair sums, and center. -/
def assembleOppositeWord {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin n) : Bool :=
  if hl : i.val < n / 2 then u ⟨i.val, hl⟩
  else if hu : i.rev.val < n / 2 then
    Bool.xor (u ⟨i.rev.val, hu⟩) (c ⟨i.rev.val, hu⟩)
  else z ⟨i.val - n / 2, center_index_of_not_outer i hl hu⟩

lemma assembleOppositeWord_lower {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    assembleOppositeWord u c z (lowerWordIndex i) = u i := by
  unfold assembleOppositeWord
  split
  · rfl
  · rename_i h
    exact (h (lowerWordIndex_lt_half i)).elim

lemma assembleOppositeWord_upper {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    assembleOppositeWord u c z (upperWordIndex i) = Bool.xor (u i) (c i) := by
  simp only [assembleOppositeWord, dite_eq_right (not_lt.mpr (half_le_upperWordIndex i)),
    upperWordIndex_rev, lowerWordIndex_val, dite_eq_left i.isLt]

lemma assembleOppositeWord_center {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n % 2)) :
    assembleOppositeWord u c z (centerWordIndex i) = z i := by
  simp only [assembleOppositeWord, centerWordIndex_rev, centerWordIndex_val,
    lt_self_iff_false, dite_false]
  congr 1
  apply Fin.ext
  have := i.isLt
  omega

lemma assembleOppositeWord_recover {n : ℕ} (w : Fin n → Bool) :
    assembleOppositeWord (fun i ↦ w (lowerWordIndex i))
      (fun i ↦ Bool.xor (w (lowerWordIndex i)) (w (upperWordIndex i)))
      (fun i ↦ w (centerWordIndex i)) = w := by
  funext i
  unfold assembleOppositeWord
  split_ifs with hl hu
  · rfl
  · dsimp only
    have h : upperWordIndex ⟨i.rev.val, hu⟩ = i := by
      change i.rev.rev = i
      exact Fin.rev_rev i
    rw [h]
    cases w (lowerWordIndex ⟨i.rev.val, hu⟩) <;> cases w i <;> rfl
  · dsimp only
    congr 1
    apply Fin.ext
    change n / 2 + (i.val - n / 2) = i.val
    omega

/-- Coordinates are pair sums, center, and lower word, in that order. -/
def oppositeWordEquiv (n : ℕ) : (Fin n → Bool) ≃
    (Fin (n / 2) → Bool) × ((Fin (n % 2) → Bool) × (Fin (n / 2) → Bool)) where
  toFun w := ⟨fun i ↦ Bool.xor (w (lowerWordIndex i)) (w (upperWordIndex i)),
    fun i ↦ w (centerWordIndex i), fun i ↦ w (lowerWordIndex i)⟩
  invFun p := assembleOppositeWord p.2.2 p.1 p.2.1
  left_inv := assembleOppositeWord_recover
  right_inv := by
    rintro ⟨c, z, u⟩
    apply Prod.ext
    · funext i
      change Bool.xor (assembleOppositeWord u c z (lowerWordIndex i))
        (assembleOppositeWord u c z (upperWordIndex i)) = c i
      rw [assembleOppositeWord_lower, assembleOppositeWord_upper]
      cases u i <;> cases c i <;> rfl
    · apply Prod.ext
      · funext i
        exact assembleOppositeWord_center u c z i
      · funext i
        exact assembleOppositeWord_lower u c z i

lemma uniformProbability_oppositeWord (n : ℕ) (E : (Fin n → Bool) → Prop) :
    uniformProbability E =
      uniformAverage (fun c : Fin (n / 2) → Bool ↦
        uniformAverage (fun z : Fin (n % 2) → Bool ↦
          uniformProbability (fun u : Fin (n / 2) → Bool ↦ E (assembleOppositeWord u c z)))) := by
  rw [← uniformProbability_equiv (oppositeWordEquiv n).symm E]
  change uniformProbability (fun p : (Fin (n / 2) → Bool) ×
      ((Fin (n % 2) → Bool) × (Fin (n / 2) → Bool)) ↦
      E (assembleOppositeWord p.2.2 p.1 p.2.1)) = _
  rw [uniformProbability_product_eq_average
    (fun (c : Fin (n / 2) → Bool)
      (p : (Fin (n % 2) → Bool) × (Fin (n / 2) → Bool)) ↦
      E (assembleOppositeWord p.2 c p.1))]
  congr 1
  funext c
  exact uniformProbability_product_eq_average (fun (z : Fin (n % 2) → Bool) (u : Fin (n / 2) → Bool) ↦
    E (assembleOppositeWord u c z))

end OdlyzkoPoonen
