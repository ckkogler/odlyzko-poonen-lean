import OdlyzkoPoonen.Probability.FiniteEvents

/-!
# A four-event expansion with a second-order remainder

Keep the three pair intersections involving a distinguished event. The error
is nonnegative and bounded by the three pair intersections among the other
events. No independence assumptions are needed.
-/

namespace OdlyzkoPoonen

theorem uniformProbability_four_event_remainder {α : Type*} [Fintype α]
    (A B C D : α → Prop) :
    let remainder := uniformProbability A + uniformProbability B +
      uniformProbability C + uniformProbability D -
      uniformProbability (fun a ↦ A a ∧ B a) -
      uniformProbability (fun a ↦ A a ∧ C a) -
      uniformProbability (fun a ↦ A a ∧ D a) -
      uniformProbability (fun a ↦ A a ∨ B a ∨ C a ∨ D a)
    0 ≤ remainder ∧ remainder ≤
      uniformProbability (fun a ↦ B a ∧ C a) +
      uniformProbability (fun a ↦ B a ∧ D a) +
      uniformProbability (fun a ↦ C a ∧ D a) := by
  classical
  dsimp only
  simp_rw [uniformProbability_eq_average_indicator]
  simp only [← uniformAverage_add, ← uniformAverage_sub]
  constructor
  · unfold uniformAverage
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro a _
    by_cases ha : A a <;> by_cases hb : B a <;>
      by_cases hc : C a <;> by_cases hd : D a <;> norm_num [ha, hb, hc, hd]
  · apply uniformAverage_mono
    intro a
    by_cases ha : A a <;> by_cases hb : B a <;>
      by_cases hc : C a <;> by_cases hd : D a <;> norm_num [ha, hb, hc, hd]

end OdlyzkoPoonen
