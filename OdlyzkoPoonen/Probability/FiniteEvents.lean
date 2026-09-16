import OdlyzkoPoonen.Probability.UniformAverage
import OdlyzkoPoonen.Probability.BinaryModel

/-!
# Unions and differences of finite events

Indicator identities give union bounds and the exact probability difference
when one event is contained in another. The results use the actual counting law,
including its empty-space convention, and introduce no measure assumptions.
-/

namespace OdlyzkoPoonen

lemma uniformAverage_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformAverage (fun a ↦ f a + g a) = uniformAverage f + uniformAverage g := by
  unfold uniformAverage
  rw [Finset.sum_add_distrib, add_div]

lemma uniformAverage_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformAverage (fun a ↦ f a - g a) = uniformAverage f - uniformAverage g := by
  unfold uniformAverage
  rw [Finset.sum_sub_distrib, sub_div]

lemma uniformProbability_or_le_add {α : Type*} [Fintype α] (E F : α → Prop) :
    uniformProbability (fun a ↦ E a ∨ F a) ≤ uniformProbability E + uniformProbability F := by
  classical
  simp_rw [uniformProbability_eq_average_indicator]
  rw [← uniformAverage_add]
  apply uniformAverage_mono
  intro a
  by_cases he : E a <;> by_cases hf : F a <;> simp [he, hf]

lemma uniformProbability_sub_of_imp {α : Type*} [Fintype α] (E F : α → Prop)
    (h : ∀ a, F a → E a) :
    uniformProbability E - uniformProbability F = uniformProbability (fun a ↦ E a ∧ ¬ F a) := by
  classical
  simp_rw [uniformProbability_eq_average_indicator]
  rw [← uniformAverage_sub]
  congr 1
  funext a
  by_cases hf : F a
  · simp [hf, h a hf]
  · simp [hf]

lemma binaryProbability_or_le_add (m : ℕ) (E F : Polynomial ℤ → Prop) :
    binaryProbability m (fun p ↦ E p ∨ F p) ≤ binaryProbability m E + binaryProbability m F :=
  uniformProbability_or_le_add (fun w ↦ E (wordPolynomial w)) (fun w ↦ F (wordPolynomial w))

end OdlyzkoPoonen
