import OdlyzkoPoonen.Probability.FiniteBounds

/-!
# Independent coordinates and conditioning on a finite product

Uniform counting on a dependent finite product gives the product of the actual
coordinate probabilities. The proof is a bijection of event subtypes, so no
independence hypothesis is needed. The conditioning bound also allows a fiber
whose possible coordinate values are unique only when the event is nonempty.
-/

namespace OdlyzkoPoonen
open scoped BigOperators Classical

lemma uniformProbability_pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (E : ∀ i, α i → Prop) :
    uniformProbability (fun w : ∀ i, α i ↦ ∀ i, E i (w i)) =
      ∏ i, uniformProbability (E i) := by
  classical
  let e : (∀ i, {a : α i // E i a}) ≃ {w : ∀ i, α i // ∀ i, E i (w i)} :=
    { toFun := fun w ↦ ⟨fun i ↦ (w i).val, fun i ↦ (w i).property⟩
      invFun := fun w i ↦ ⟨w.val i, w.property i⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hc := Fintype.card_congr e
  unfold uniformProbability
  simp only [← Fintype.card_subtype]
  rw [← hc, Fintype.card_pi, Fintype.card_pi]
  simp only [Nat.cast_prod, Finset.prod_div_distrib]

lemma uniformProbability_pi_eq_le {ι : Type*} [Fintype ι] {α β : ι → Type*}
    [∀ i, Fintype (α i)] (f : ∀ i, α i → β i) (c : ι → ℝ)
    (hc : ∀ i y, uniformProbability (fun a ↦ f i a = y) ≤ c i)
    (y : ∀ i, β i) :
    uniformProbability (fun w : ∀ i, α i ↦ ∀ i, f i (w i) = y i) ≤ ∏ i, c i := by
  rw [uniformProbability_pi (fun i a ↦ f i a = y i)]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ uniformProbability_nonneg _)
    (fun i _ ↦ hc i (y i))

lemma uniformProbability_fiber_unique_le {ι γ : Type*} [Fintype ι]
    [Fintype γ] [Nonempty γ] {α β : ι → Type*} [∀ i, Fintype (α i)]
    (E : γ → (∀ i, α i) → Prop) (f : ∀ i, α i → β i) (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i)
    (hc : ∀ i y, uniformProbability (fun a ↦ f i a = y) ≤ c i)
    (hunique : ∀ x w v, E x w → E x v → ∀ i, f i (w i) = f i (v i)) :
    uniformProbability (fun v : γ × (∀ i, α i) ↦ E v.1 v.2) ≤ ∏ i, c i := by
  classical
  rw [uniformProbability_product_eq_average]
  calc
    _ ≤ uniformAverage (fun _ : γ ↦ ∏ i, c i) := by
      apply uniformAverage_mono
      intro x
      by_cases he : ∃ v, E x v
      · obtain ⟨v, hv⟩ := he
        calc
          _ ≤ uniformProbability (fun w : ∀ i, α i ↦ ∀ i, f i (w i) = f i (v i)) :=
            uniformProbability_mono (fun w hw ↦ hunique x w v hw hv)
          _ ≤ _ := uniformProbability_pi_eq_le f c hc (fun i ↦ f i (v i))
      · have hf : E x = (fun _ ↦ False) := by
          funext w
          exact propext ⟨fun hw ↦ he ⟨w, hw⟩, False.elim⟩
        rw [hf, uniformProbability_false]
        exact Finset.prod_nonneg (fun i _ ↦ hc0 i)
    _ = _ := uniformAverage_const _

end OdlyzkoPoonen
