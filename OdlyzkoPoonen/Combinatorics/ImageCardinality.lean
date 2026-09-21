import Mathlib.Data.Finset.Card

/-!
# Finite images with the same fibers

Changing the representation of a finite invariant preserves the number of
values whenever equality of the old and new representations is equivalent.
-/

namespace OdlyzkoPoonen

lemma card_image_le_of_fiber_imp {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ a ∈ s, ∀ b ∈ s, g a = g b → f a = f b) :
    (s.image f).card ≤ (s.image g).card := by
  classical
  let pick (y : {y // y ∈ s.image f}) : α := (Finset.mem_image.mp y.property).choose
  have hp (y : {y // y ∈ s.image f}) : pick y ∈ s ∧ f (pick y) = y.val :=
    (Finset.mem_image.mp y.property).choose_spec
  let F : {y // y ∈ s.image f} → {z // z ∈ s.image g} :=
    fun y ↦ ⟨g (pick y), Finset.mem_image_of_mem g (hp y).1⟩
  apply Finset.card_le_card_of_injective (f := F)
  intro a b hab
  apply Subtype.ext
  calc
    a.val = f (pick a) := (hp a).2.symm
    _ = f (pick b) := h _ (hp a).1 _ (hp b).1 (congrArg Subtype.val hab)
    _ = b.val := (hp b).2

/-- Two representations with equivalent equality tests have equally large
finite images. -/
theorem card_image_eq_of_fibers_iff {α β γ : Type*}
    [DecidableEq β] [DecidableEq γ] (s : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ g a = g b) :
    (s.image f).card = (s.image g).card := by
  apply Nat.le_antisymm
  · exact card_image_le_of_fiber_imp s f g (fun a ha b hb ↦ (h a ha b hb).mpr)
  · exact card_image_le_of_fiber_imp s g f (fun a ha b hb ↦ (h a ha b hb).mp)

end OdlyzkoPoonen
