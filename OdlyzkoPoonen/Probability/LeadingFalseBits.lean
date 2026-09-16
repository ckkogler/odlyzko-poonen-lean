import OdlyzkoPoonen.Probability.BitWeights

/-!
# Removing initial false bits

Shifting past a block of false coordinates leaves the number of true bits
unchanged. The result is an exact finite cardinality identity, including an
empty suffix.
-/

namespace OdlyzkoPoonen

/-- Embed the suffix after `j` initial coordinates into the full word. -/
def shiftedWordIndex {m j : ℕ} (hj : j ≤ m) (i : Fin (m - j)) : Fin m :=
  ⟨j + i.val, by have := i.isLt; omega⟩

lemma shiftedWordIndex_injective {m j : ℕ} (hj : j ≤ m) :
    Function.Injective (shiftedWordIndex hj) := by
  intro i k h
  apply Fin.ext
  have hval := congrArg Fin.val h
  change j + i.val = j + k.val at hval
  omega

lemma trueBitCount_eq_shifted {m j : ℕ} (hj : j ≤ m) (w : Fin m → Bool)
    (hzero : ∀ i : Fin m, i.val < j → w i = false) :
    trueBitCount w = trueBitCount (fun i : Fin (m - j) ↦ w (shiftedWordIndex hj i)) := by
  classical
  unfold trueBitCount
  symm
  apply Finset.card_bij (fun i _ ↦ shiftedWordIndex hj i)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  · intro i _ k _ h
    exact shiftedWordIndex_injective hj h
  · intro i hi
    have htrue := (Finset.mem_filter.mp hi).2
    have hji : j ≤ i.val := by
      by_contra h
      have hf := hzero i (by omega)
      rw [htrue] at hf
      contradiction
    let k : Fin (m - j) := ⟨i.val - j, by have := i.isLt; omega⟩
    have heq : shiftedWordIndex hj k = i := by
      apply Fin.ext
      dsimp [shiftedWordIndex, k]
      omega
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, heq⟩
    change w (shiftedWordIndex hj k) = true
    rw [heq]
    exact htrue

end OdlyzkoPoonen
