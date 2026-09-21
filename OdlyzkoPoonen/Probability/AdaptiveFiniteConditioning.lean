import OdlyzkoPoonen.Probability.SelectedCoordinates
import OdlyzkoPoonen.Probability.FiniteSetUnion

/-!
# Conditioning with a finite family of possible witnesses

A statistic may select a different finite family in each conditioning fiber.
If the statistic is fixed by the unexposed coordinates and each witness permits
at most one exposed Boolean word, the event has probability at most the family
size times the mass of one exposed word.
-/

namespace OdlyzkoPoonen
open scoped BigOperators Classical

lemma uniformProbability_singleton {α : Type*} [Fintype α] (a : α) :
    uniformProbability (fun b : α ↦ b = a) = 1 / (Fintype.card α : ℝ) := by
  have h : Finset.univ.filter (fun b : α ↦ b = a) = {a} := by
    ext b
    simp
  rw [uniformProbability, h]
  simp

lemma uniformProbability_subsingleton_le {α : Type*} [Fintype α]
    (E : α → Prop) (h : ∀ a b, E a → E b → a = b) :
    uniformProbability E ≤ 1 / (Fintype.card α : ℝ) := by
  by_cases he : ∃ a, E a
  · obtain ⟨a, ha⟩ := he
    calc
      _ ≤ uniformProbability (fun b : α ↦ b = a) :=
        uniformProbability_mono (fun b hb ↦ h b a hb ha)
      _ = _ := uniformProbability_singleton a
  · have hf : E = (fun _ ↦ False) := by
      funext a
      exact propext ⟨fun ha ↦ he ⟨a, ha⟩, False.elim⟩
    rw [hf, uniformProbability_false]
    positivity

lemma uniformProbability_adaptive_selected_le {ι κ σ : Type*}
    [Fintype ι] [DecidableEq ι] (s : ι → Prop)
    (statistic : (ι → Bool) → σ) (family : σ → Finset κ)
    (E : κ → (ι → Bool) → Prop) (M : ℕ)
    (hcard : ∀ a, (family a).card ≤ M)
    (hstat : ∀ w v, (∀ i, ¬s i → w i = v i) → statistic w = statistic v)
    (hunique : ∀ k w v, E k w → E k v →
      (∀ i, ¬s i → w i = v i) → w = v) :
    uniformProbability (fun w ↦ ∃ k ∈ family (statistic w), E k w) ≤
      M * (1 / 2 : ℝ) ^ Fintype.card {i : ι // s i} := by
  let γ := {i : ι // ¬s i} → Bool
  let δ := {i : ι // s i} → Bool
  let e : (ι → Bool) ≃ γ × δ :=
    (Equiv.piEquivPiSubtypeProd s (fun _ ↦ Bool)).trans (Equiv.prodComm _ _)
  rw [← uniformProbability_equiv e.symm]
  change uniformProbability (fun p : γ × δ ↦
    ∃ k ∈ family (statistic (e.symm p)), E k (e.symm p)) ≤ _
  rw [uniformProbability_product_eq_average (fun (x : γ) (v : δ) ↦
    ∃ k ∈ family (statistic (e.symm (x, v))), E k (e.symm (x, v)))]
  apply uniformAverage_le
  intro x
  let w₀ := e.symm (x, fun _ ↦ false)
  have hsame (v w : δ) (i : ι) (hi : ¬s i) :
      e.symm (x, v) i = e.symm (x, w) i := by
    simp [e, Equiv.piEquivPiSubtypeProd, hi]
  have hs (v : δ) : statistic (e.symm (x, v)) = statistic w₀ :=
    hstat _ _ (hsame v (fun _ ↦ false))
  simp_rw [hs]
  calc
    _ ≤ (family (statistic w₀)).card * (1 / (Fintype.card δ : ℝ)) := by
      apply uniformProbability_exists_mem_le_card_mul
      intro k _
      apply uniformProbability_subsingleton_le
      intro v w hv hw
      have he := hunique k (e.symm (x, v)) (e.symm (x, w)) hv hw (hsame v w)
      have := congrArg (fun a ↦ (e a).2) he
      simpa using this
    _ ≤ M * (1 / (Fintype.card δ : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard (statistic w₀)
      · positivity
    _ = _ := by simp [δ]

end OdlyzkoPoonen
