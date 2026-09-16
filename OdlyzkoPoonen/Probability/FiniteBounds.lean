import OdlyzkoPoonen.Probability.AverageBounds

/-!
# Finite union and fiber bounds

Finite probability bounds follow from ordinary indicator sums. A uniform bound
on every fiber of an event multiplies by the probability of its base event.
These lemmas keep later polynomial estimates on the actual finite product law.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma uniformAverage_sum {α β : Type*} [Fintype α] [Fintype β] (f : β → α → ℝ) :
    uniformAverage (fun a ↦ ∑ b, f b a) = ∑ b, uniformAverage (f b) := by
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

lemma uniformAverage_mul_right {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    uniformAverage (fun a ↦ f a * c) = uniformAverage f * c := by
  unfold uniformAverage
  rw [← Finset.sum_mul]
  ring

lemma uniformProbability_exists_le_sum {α β : Type*} [Fintype α] [Fintype β]
    (E : β → α → Prop) :
    uniformProbability (fun a ↦ ∃ b, E b a) ≤ ∑ b, uniformProbability (E b) := by
  classical
  simp_rw [uniformProbability_eq_average_indicator]
  rw [← uniformAverage_sum]
  apply uniformAverage_mono
  intro a
  by_cases h : ∃ b, E b a
  · rw [ite_eq_left h]
    obtain ⟨b, hb⟩ := h
    have hle := Finset.single_le_sum
      (f := fun b ↦ if E b a then (1 : ℝ) else 0)
      (fun _ _ ↦ by positivity) (Finset.mem_univ b)
    simpa only [ite_eq_left hb] using hle
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun _ _ ↦ by positivity)

lemma uniformProbability_product_bound {α β : Type*} [Fintype α] [Fintype β]
    (F : α → Prop) (E : α → β → Prop) (c : ℝ)
    (h : ∀ a, F a → uniformProbability (E a) ≤ c) :
    uniformProbability (fun v : α × β ↦ F v.1 ∧ E v.1 v.2) ≤ uniformProbability F * c := by
  classical
  rw [uniformProbability_product_eq_average (fun (a : α) (b : β) ↦ F a ∧ E a b)]
  calc
    _ ≤ uniformAverage (fun a : α ↦ (if F a then 1 else 0) * c) := by
      apply uniformAverage_mono
      intro a
      by_cases ha : F a
      · have heq : (fun b : β ↦ F a ∧ E a b) = E a := by funext b; simp [ha]
        rw [heq, ite_eq_left ha, one_mul]
        exact h a ha
      · have heq : (fun b : β ↦ F a ∧ E a b) = (fun _ : β ↦ False) := by funext b; simp [ha]
        rw [heq, uniformProbability_false, ite_eq_right ha, zero_mul]
    _ = _ := by
      rw [uniformAverage_mul_right, ← uniformProbability_eq_average_indicator]

end OdlyzkoPoonen
