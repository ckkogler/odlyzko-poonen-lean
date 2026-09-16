import OdlyzkoPoonen.Probability.FiniteProduct

/-!
# Conditioning on unselected coordinates

Suppose that, once all unselected coordinates are fixed, an event determines
the value of a statistic of each selected coordinate. Its probability is at
most the product of uniform atom bounds for those statistics. Coordinate
spaces and statistics may vary with the index.
-/

namespace OdlyzkoPoonen
open scoped BigOperators Classical

lemma uniformProbability_selected_coordinates_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (s : ι → Prop) (E : (∀ i, α i) → Prop)
    (f : ∀ i, α i → β i) (c : ι → ℝ)
    (hc0 : ∀ i, s i → 0 ≤ c i)
    (hc : ∀ i, s i → ∀ y, uniformProbability (fun a ↦ f i a = y) ≤ c i)
    (hunique : ∀ w v, E w → E v → (∀ i, ¬s i → w i = v i) →
      ∀ i, s i → f i (w i) = f i (v i)) :
    uniformProbability E ≤ ∏ i : {i : ι // s i}, c i.val := by
  letI : DecidableEq {i : ι // s i} := Classical.decEq _
  letI : DecidableEq {i : ι // ¬s i} := Classical.decEq _
  let γ := ∀ i : {i : ι // ¬s i}, α i.val
  let δ := ∀ i : {i : ι // s i}, α i.val
  let e : (∀ i, α i) ≃ γ × δ :=
    (Equiv.piEquivPiSubtypeProd s α).trans (Equiv.prodComm _ _)
  calc
    _ = uniformProbability (fun v : γ × δ ↦ E (e.symm v)) :=
      (uniformProbability_equiv (α := γ × δ) (β := ∀ i, α i) e.symm E).symm
    _ ≤ _ := by
      apply uniformProbability_fiber_unique_le
        (fun x w ↦ E (e.symm (x, w)))
        (fun (i : {i : ι // s i}) ↦ f i.val) (fun i ↦ c i.val)
        (fun i ↦ hc0 i.val i.property) (fun i ↦ hc i.val i.property)
      intro x w v hw hv i
      have h := hunique (e.symm (x, w)) (e.symm (x, v)) hw hv
        (fun j hj ↦ by simp [e, Equiv.piEquivPiSubtypeProd, hj]) i.val i.property
      simpa [e, Equiv.piEquivPiSubtypeProd, i.property] using h

end OdlyzkoPoonen
