import OdlyzkoPoonen.Probability.PrescribedBits
import Mathlib.Order.Interval.Finset.Fin

/-!
# The first true bit of a uniform word

A first true bit at zero-based index `i` prescribes `i+1` bits and therefore
has probability `2^(-(i+1))`. The event is unique when it exists, and it exists
exactly when the word is not identically false. These finite facts will identify
the first asymmetric opposite pair of a random polynomial.
-/

namespace OdlyzkoPoonen

/-- The bit at `i` is true and every earlier bit is false. -/
def FirstTrueAt {n : ℕ} (w : Fin n → Bool) (i : Fin n) : Prop :=
  w i = true ∧ ∀ j < i, w j = false

lemma firstTrueAt_iff_prescribed {n : ℕ} (w : Fin n → Bool) (i : Fin n) :
    FirstTrueAt w i ↔ ∀ j ∈ Finset.Iic i, w j = if j = i then true else false := by
  constructor
  · rintro ⟨hi, hprev⟩ j hj
    have hji := Finset.mem_Iic.mp hj
    by_cases heq : j = i
    · simpa only [heq, ite_true] using hi
    · simpa only [ite_eq_right heq] using hprev j (lt_of_le_of_ne hji heq)
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using h i (Finset.mem_Iic.mpr le_rfl)
    · intro j hj
      simpa only [ite_eq_right (ne_of_lt hj)] using h j (Finset.mem_Iic.mpr hj.le)

lemma uniformProbability_firstTrueAt {n : ℕ} (i : Fin n) :
    uniformProbability (fun w : Fin n → Bool ↦ FirstTrueAt w i) =
      (1 / 2 : ℝ) ^ (i.val + 1) := by
  simp only [firstTrueAt_iff_prescribed]
  rw [uniformProbability_prescribedBits, Fin.card_Iic]

lemma FirstTrueAt.unique {n : ℕ} {w : Fin n → Bool} {i j : Fin n}
    (hi : FirstTrueAt w i) (hj : FirstTrueAt w j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hf := hj.2 i h
    rw [hi.1] at hf
    contradiction
  · exact h
  · have hf := hi.2 j h
    rw [hj.1] at hf
    contradiction

lemma exists_firstTrueAt_iff {n : ℕ} (w : Fin n → Bool) :
    (∃ i, FirstTrueAt w i) ↔ ¬ ∀ i, w i = false := by
  classical
  constructor
  · rintro ⟨i, hi⟩ h
    have := h i
    rw [hi.1] at this
    contradiction
  · intro h
    have hex : ∃ i, w i = true := by
      push Not at h
      obtain ⟨i, hi⟩ := h
      refine ⟨i, ?_⟩
      cases heq : w i
      · exact (hi heq).elim
      · rfl
    let s := Finset.univ.filter (fun i ↦ w i = true)
    have hs : s.Nonempty := by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    refine ⟨s.min' hs, (Finset.mem_filter.mp (s.min'_mem hs)).2, ?_⟩
    intro j hj
    cases heq : w j
    · rfl
    · have hmem : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
      exact (not_lt_of_ge (s.min'_le j hmem) hj).elim

end OdlyzkoPoonen
