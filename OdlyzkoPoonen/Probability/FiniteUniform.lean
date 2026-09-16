import Mathlib.Tactic

/-!
# Uniform finite counting probability

Probabilities are real cardinality ratios. The product identity derives
independence directly from counting, including the empty-type convention.
Normalization is stated for nonempty finite spaces.
-/

namespace OdlyzkoPoonen

/-- The actual uniform counting probability of a predicate on a finite type. -/
noncomputable def uniformProbability {α : Type*} [Fintype α] (E : α → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter E).card : ℝ) / Fintype.card α

lemma uniformProbability_false {α : Type*} [Fintype α] :
    uniformProbability (fun _ : α ↦ False) = 0 := by
  classical
  simp [uniformProbability]

lemma uniformProbability_true {α : Type*} [Fintype α] [Nonempty α] :
    uniformProbability (fun _ : α ↦ True) = 1 := by
  classical
  simp [uniformProbability, Fintype.card_ne_zero]

lemma uniformProbability_nonneg {α : Type*} [Fintype α] (E : α → Prop) :
    0 ≤ uniformProbability E := by
  unfold uniformProbability
  positivity

lemma uniformProbability_mono {α : Type*} [Fintype α] {E F : α → Prop}
    (h : ∀ a, E a → F a) : uniformProbability E ≤ uniformProbability F := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, h a (Finset.mem_filter.mp ha).2⟩

lemma uniformProbability_le_one {α : Type*} [Fintype α] [Nonempty α] (E : α → Prop) :
    uniformProbability E ≤ 1 := by
  calc
    uniformProbability E ≤ uniformProbability (fun _ : α ↦ True) :=
      uniformProbability_mono (fun _ _ ↦ trivial)
    _ = 1 := uniformProbability_true

lemma uniformProbability_product {α β : Type*} [Fintype α] [Fintype β]
    (E : α → Prop) (F : β → Prop) :
    uniformProbability (fun p : α × β ↦ E p.1 ∧ F p.2) =
      uniformProbability E * uniformProbability F := by
  classical
  letI : DecidablePred (fun p : α × β ↦ E p.1 ∧ F p.2) :=
    fun _ ↦ Classical.propDecidable _
  have h : Finset.univ.filter (fun p : α × β ↦ E p.1 ∧ F p.2) =
      (Finset.univ.filter E) ×ˢ (Finset.univ.filter F) := by
    ext p
    simp
  unfold uniformProbability
  rw [h, Finset.card_product, Fintype.card_prod]
  push_cast
  ring

end OdlyzkoPoonen
