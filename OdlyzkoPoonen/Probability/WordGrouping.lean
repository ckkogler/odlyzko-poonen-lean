import OdlyzkoPoonen.Probability.FiniteProduct

/-!
# Grouping a uniform word into disjoint blocks

The fibers of an arbitrary index map partition the free bits. Restriction to
these fibers is an equivalence of the complete word spaces, and consequently
the block laws are the actual independent uniform counting laws.
-/

namespace OdlyzkoPoonen
open scoped BigOperators Classical

/-- A word is exactly its family of restrictions to fibers of an index map. -/
def groupWordEquiv {ι κ : Type*} (f : ι → κ) :
    (ι → Bool) ≃ (∀ j : κ, {i : ι // f i = j} → Bool) :=
  Equiv.piCongrFiberwise (f := f) (fun _ ↦ Equiv.refl _)

lemma groupWordEquiv_apply {ι κ : Type*} (f : ι → κ) (w : ι → Bool)
    (j : κ) (i : {i : ι // f i = j}) : groupWordEquiv f w j i = w i.val := rfl

lemma uniformProbability_groupWord {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (E : (∀ j : κ, {i : ι // f i = j} → Bool) → Prop) :
    uniformProbability (fun w : ι → Bool ↦ E (groupWordEquiv f w)) =
      uniformProbability E := uniformProbability_equiv (groupWordEquiv f) E

lemma uniformProbability_groupWord_pi {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (E : ∀ j : κ, ({i : ι // f i = j} → Bool) → Prop) :
    uniformProbability (fun w : ι → Bool ↦ ∀ j, E j (fun i ↦ w i.val)) =
      ∏ j, uniformProbability (E j) := by
  calc
    _ = uniformProbability (fun v : ∀ j : κ, {i : ι // f i = j} → Bool ↦ ∀ j, E j (v j)) :=
      uniformProbability_groupWord f _
    _ = _ := uniformProbability_pi E

end OdlyzkoPoonen
