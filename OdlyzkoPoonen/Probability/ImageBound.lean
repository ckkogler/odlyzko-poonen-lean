import OdlyzkoPoonen.Probability.FiniteUniform

/-!
# Counting images of witnesses

When an event in an injectively represented finite space is covered by images
of witnesses in another finite space, its cardinality is at most the witness
cardinality. Dividing by the two actual space sizes gives the probability bound.
No injectivity of the witness map is assumed.
-/

namespace OdlyzkoPoonen

lemma uniformProbability_exists_image_le {α β γ : Type*}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → γ) (g : β → γ) (hg : Function.Injective g) (E : α → Prop) :
    uniformProbability (fun b : β ↦ ∃ a : α, E a ∧ g b = f a) ≤
      uniformProbability E * ((Fintype.card α : ℝ) / Fintype.card β) := by
  classical
  letI : DecidablePred E := fun _ ↦ Classical.propDecidable _
  letI : DecidablePred (fun b : β ↦ ∃ a : α, E a ∧ g b = f a) :=
    fun _ ↦ Classical.propDecidable _
  have hcard : (Finset.univ.filter (fun b : β ↦ ∃ a : α, E a ∧ g b = f a)).card ≤
      (Finset.univ.filter E).card := by
    calc
      _ = ((Finset.univ.filter (fun b : β ↦ ∃ a : α, E a ∧ g b = f a)).image g).card :=
        (Finset.card_image_of_injective _ hg).symm
      _ ≤ ((Finset.univ.filter E).image f).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨a, ha, heq⟩ := (Finset.mem_filter.mp hb).2
        exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, heq.symm⟩
      _ ≤ _ := Finset.card_image_le
  unfold uniformProbability
  have hα : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    _ ≤ ((Finset.univ.filter E).card : ℝ) / Fintype.card β :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
    _ = _ := by field_simp

end OdlyzkoPoonen
