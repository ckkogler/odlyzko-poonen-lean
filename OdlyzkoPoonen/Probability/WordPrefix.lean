import OdlyzkoPoonen.Probability.AverageBounds

/-!
# Uniform prefixes of finite words

Splitting a Boolean word into a prefix and its remaining suffix is an explicit
bijection. Consequently averaging a function of the prefix alone agrees with
averaging that function over uniform shorter words. Empty prefixes and suffixes
are included.
-/

namespace OdlyzkoPoonen

/-- Restrict to the first `r` coordinates of a word of length `m`. -/
def wordPrefix {m r : ℕ} (hr : r ≤ m) (w : Fin m → Bool) : Fin r → Bool :=
  fun i ↦ w ⟨i.val, lt_of_lt_of_le i.isLt hr⟩

/-- A word is its prefix together with its suffix. -/
def prefixWordEquiv {m r : ℕ} (hr : r ≤ m) :
    (Fin m → Bool) ≃ (Fin r → Bool) × (Fin (m - r) → Bool) where
  toFun w := ⟨wordPrefix hr w, fun i ↦ w ⟨r + i.val, by have := i.isLt; omega⟩⟩
  invFun v i := if hi : i.val < r then v.1 ⟨i.val, hi⟩
    else v.2 ⟨i.val - r, by have := i.isLt; omega⟩
  left_inv w := by
    funext i
    dsimp only [wordPrefix]
    split_ifs with hi
    · rfl
    · congr 1
      apply Fin.ext
      dsimp only
      omega
  right_inv v := by
    apply Prod.ext
    · funext i
      dsimp only [wordPrefix]
      split
      · rfl
      · rename_i h
        exact (h i.isLt).elim
    · funext i
      dsimp only
      rw [dite_eq_right (show ¬ r + i.val < r by omega)]
      apply congrArg v.2
      apply Fin.ext
      dsimp only
      omega

lemma uniformAverage_wordPrefix {m r : ℕ} (hr : r ≤ m) (f : (Fin r → Bool) → ℝ) :
    uniformAverage (fun w : Fin m → Bool ↦ f (wordPrefix hr w)) = uniformAverage f := by
  calc
    _ = uniformAverage (fun v : (Fin r → Bool) × (Fin (m - r) → Bool) ↦ f v.1) :=
      uniformAverage_equiv (prefixWordEquiv hr) (fun v ↦ f v.1)
    _ = _ := by
      rw [uniformAverage_product (fun (v : Fin r → Bool) (_ : Fin (m - r) → Bool) ↦ f v)]
      simp only [uniformAverage_const]

end OdlyzkoPoonen
