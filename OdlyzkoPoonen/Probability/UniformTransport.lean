import OdlyzkoPoonen.Probability.FiniteUniform

/-!
# Transport of uniform counting probability

A bijection between finite spaces identifies their actual uniform probabilities.
The proof counts the corresponding event subtypes; it does not posit invariance
as part of the probability model.
-/

namespace OdlyzkoPoonen

lemma uniformProbability_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (E : β → Prop) :
    uniformProbability (fun a ↦ E (e a)) = uniformProbability E := by
  classical
  have h : Fintype.card {a : α // E (e a)} = Fintype.card {b : β // E b} :=
    Fintype.card_congr (e.subtypeEquiv (fun _ ↦ Iff.rfl))
  unfold uniformProbability
  rw [← Fintype.card_subtype, ← Fintype.card_subtype, h, Fintype.card_congr e]

lemma uniformProbability_bijective {α β : Type*} [Fintype α] [Fintype β]
    {f : α → β} (hf : Function.Bijective f) (E : β → Prop) :
    uniformProbability (fun a ↦ E (f a)) = uniformProbability E :=
  uniformProbability_equiv (Equiv.ofBijective f hf) E

end OdlyzkoPoonen
