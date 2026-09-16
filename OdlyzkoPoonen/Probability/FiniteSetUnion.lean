import OdlyzkoPoonen.Probability.FiniteBounds

/-!
# Finite union bounds with a finite set of witnesses

The witness type need not be finite: it suffices to specify a finite set of
possible witnesses. Ordinary indicator sums give the union bound, including
an empty witness set. This form applies directly to finite polynomial families.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma uniformAverage_finset_sum {α β : Type*} [Fintype α]
    (s : Finset β) (f : β → α → ℝ) :
    uniformAverage (fun a ↦ ∑ b ∈ s, f b a) = ∑ b ∈ s, uniformAverage (f b) := by
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

lemma uniformProbability_exists_mem_le_sum {α β : Type*} [Fintype α]
    (s : Finset β) (E : β → α → Prop) :
    uniformProbability (fun a ↦ ∃ b ∈ s, E b a) ≤ ∑ b ∈ s, uniformProbability (E b) := by
  classical
  simp_rw [uniformProbability_eq_average_indicator]
  rw [← uniformAverage_finset_sum]
  apply uniformAverage_mono
  intro a
  by_cases h : ∃ b ∈ s, E b a
  · rw [ite_eq_left h]
    obtain ⟨b, hbs, hb⟩ := h
    have hle := Finset.single_le_sum
      (f := fun b ↦ if E b a then (1 : ℝ) else 0)
      (fun _ _ ↦ by positivity) hbs
    simpa only [ite_eq_left hb] using hle
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun _ _ ↦ by positivity)

lemma uniformProbability_exists_mem_le_card_mul {α β : Type*} [Fintype α]
    (s : Finset β) (E : β → α → Prop) (c : ℝ)
    (h : ∀ b ∈ s, uniformProbability (E b) ≤ c) :
    uniformProbability (fun a ↦ ∃ b ∈ s, E b a) ≤ s.card * c := by
  calc
    _ ≤ ∑ b ∈ s, uniformProbability (E b) := uniformProbability_exists_mem_le_sum s E
    _ ≤ ∑ _b ∈ s, c := Finset.sum_le_sum h
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

end OdlyzkoPoonen
