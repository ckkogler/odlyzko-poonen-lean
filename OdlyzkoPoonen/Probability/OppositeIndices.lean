import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

/-!
# Opposite positions in a finite word

A word of length `n` has `n/2` opposite pairs and `n%2` central positions.
The lower and upper embeddings are related by `Fin.rev`. All definitions and
bounds include an empty word; a central position exists only for odd length.
-/

namespace OdlyzkoPoonen

/-- Lower position of an opposite pair. -/
def lowerWordIndex {n : ℕ} (i : Fin (n / 2)) : Fin n :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- Upper position of an opposite pair. -/
def upperWordIndex {n : ℕ} (i : Fin (n / 2)) : Fin n :=
  (lowerWordIndex i).rev

/-- The central position, indexed by `Fin (n%2)`. -/
def centerWordIndex {n : ℕ} (i : Fin (n % 2)) : Fin n :=
  ⟨n / 2 + i.val, by have := i.isLt; omega⟩

lemma lowerWordIndex_val {n : ℕ} (i : Fin (n / 2)) :
    (lowerWordIndex i).val = i.val := rfl

lemma upperWordIndex_val {n : ℕ} (i : Fin (n / 2)) :
    (upperWordIndex i).val = n - (i.val + 1) := by
  simp [upperWordIndex, lowerWordIndex, Fin.val_rev]

lemma lowerWordIndex_lt_half {n : ℕ} (i : Fin (n / 2)) :
    (lowerWordIndex i).val < n / 2 := i.isLt

lemma half_le_upperWordIndex {n : ℕ} (i : Fin (n / 2)) :
    n / 2 ≤ (upperWordIndex i).val := by
  rw [upperWordIndex_val]
  have := i.isLt
  omega

lemma upperWordIndex_rev {n : ℕ} (i : Fin (n / 2)) :
    (upperWordIndex i).rev = lowerWordIndex i := by
  simp [upperWordIndex]

lemma centerWordIndex_val {n : ℕ} (i : Fin (n % 2)) :
    (centerWordIndex i).val = n / 2 := by
  have := i.isLt
  have : i.val = 0 := by omega
  simp [centerWordIndex, this]

lemma centerWordIndex_rev {n : ℕ} (i : Fin (n % 2)) :
    (centerWordIndex i).rev = centerWordIndex i := by
  apply Fin.ext
  rw [Fin.val_rev, centerWordIndex_val]
  have := i.isLt
  omega

lemma center_index_of_not_outer {n : ℕ} (i : Fin n)
    (hl : ¬ i.val < n / 2) (hu : ¬ i.rev.val < n / 2) :
    i.val - n / 2 < n % 2 := by
  have := i.isLt
  rw [Fin.val_rev] at hu
  omega

end OdlyzkoPoonen
