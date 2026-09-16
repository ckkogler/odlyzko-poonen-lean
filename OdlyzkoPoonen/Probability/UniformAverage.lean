import OdlyzkoPoonen.Probability.UniformTransport

/-!
# Finite uniform averages and fiber probabilities

These are ordinary real sums divided by the size of a finite type. The fiber
identity computes a probability on a product by averaging probabilities on its
fibers, providing the finite counting form of conditioning used in exposure.
-/

namespace OdlyzkoPoonen
open scoped BigOperators Classical

/-- Arithmetic mean on a finite type, with value zero for an empty type. -/
noncomputable def uniformAverage {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

lemma uniformAverage_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformAverage f ≤ uniformAverage g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun a _ ↦ h a)

lemma uniformAverage_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) :
    uniformAverage (fun a ↦ f (e a)) = uniformAverage f := by
  unfold uniformAverage
  rw [e.sum_comp, Fintype.card_congr e]

lemma uniformAverage_bijective {α β : Type*} [Fintype α] [Fintype β]
    {e : α → β} (he : Function.Bijective e) (f : β → ℝ) :
    uniformAverage (fun a ↦ f (e a)) = uniformAverage f :=
  uniformAverage_equiv (Equiv.ofBijective e he) f

lemma uniformAverage_product {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformAverage (fun p : α × β ↦ f p.1 p.2) =
      uniformAverage (fun a ↦ uniformAverage (f a)) := by
  unfold uniformAverage
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    Finset.sum_div, div_div]
  rw [mul_comm (Fintype.card α : ℝ)]

lemma uniformProbability_eq_average_indicator {α : Type*} [Fintype α]
    (E : α → Prop) :
    uniformProbability E = uniformAverage (fun a ↦ if E a then 1 else 0) := by
  classical
  simp [uniformProbability, uniformAverage]

lemma uniformProbability_product_eq_average {α β : Type*} [Fintype α] [Fintype β]
    (E : α → β → Prop) :
    uniformProbability (fun p : α × β ↦ E p.1 p.2) =
      uniformAverage (fun a ↦ uniformProbability (E a)) := by
  rw [uniformProbability_eq_average_indicator,
    uniformAverage_product (fun a b ↦ if E a b then 1 else 0)]
  congr 1
  funext a
  exact (uniformProbability_eq_average_indicator (E a)).symm

end OdlyzkoPoonen
