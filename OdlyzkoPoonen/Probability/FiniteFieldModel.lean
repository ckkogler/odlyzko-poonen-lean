import OdlyzkoPoonen.FiniteField.BinaryFamily
import OdlyzkoPoonen.Probability.BinaryModel

/-!
# Uniform finite-field polynomial models

Uniform internal bits give the uniform law on the actual finite-field endpoint
family. The pair model uses the Cartesian product of the two word spaces;
its independence is a consequence of counting and is not an assumption.
-/

open scoped Classical

namespace OdlyzkoPoonen

/-- The uniform finite-field endpoint law with `m` internal coefficients. -/
noncomputable def f2Probability (m : ℕ) (E : Polynomial (ZMod 2) → Prop) : ℝ :=
  uniformProbability (fun w : Fin m → Bool ↦ E (f2WordPolynomial w))

lemma f2Probability_eq_count (m : ℕ) (E : Polynomial (ZMod 2) → Prop) :
    f2Probability m E = ((f2Family m).filter E).card / (2 : ℝ) ^ m := by
  classical
  have h : (Finset.univ.filter (fun w : Fin m → Bool ↦ E (f2WordPolynomial w))).image
      f2WordPolynomial = (f2Family m).filter E := by
    ext p
    simp only [f2Family, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, rfl⟩, hw⟩
    · rintro ⟨⟨w, rfl⟩, hw⟩
      exact ⟨w, hw, rfl⟩
  rw [f2Probability, uniformProbability, ← h,
    Finset.card_image_of_injective _ f2WordPolynomial_injective]
  simp

lemma f2Probability_eq_binaryProbability (m : ℕ) (E : Polynomial (ZMod 2) → Prop) :
    f2Probability m E = binaryProbability m (fun p ↦ E (reducePolynomial 2 p)) := rfl

lemma f2Probability_endpoints (m : ℕ) :
    f2Probability m (HasF2Endpoints (m + 1)) = 1 := by
  unfold f2Probability
  have h : (fun w : Fin m → Bool ↦ HasF2Endpoints (m + 1) (f2WordPolynomial w)) =
      (fun _ ↦ True) := by
    funext w
    exact propext ⟨fun _ ↦ trivial, fun _ ↦ f2WordPolynomial_endpoints w⟩
  rw [h, uniformProbability_true]

/-- Independently chosen finite-field endpoint polynomials, represented by their
respective uniform internal words. -/
noncomputable def f2PairProbability (m l : ℕ)
    (E : Polynomial (ZMod 2) → Polynomial (ZMod 2) → Prop) : ℝ :=
  uniformProbability (fun w : (Fin m → Bool) × (Fin l → Bool) ↦
    E (f2WordPolynomial w.1) (f2WordPolynomial w.2))

lemma f2PairProbability_product (m l : ℕ)
    (E F : Polynomial (ZMod 2) → Prop) :
    f2PairProbability m l (fun a b ↦ E a ∧ F b) =
      f2Probability m E * f2Probability l F := by
  unfold f2PairProbability f2Probability
  exact uniformProbability_product
    (fun w : Fin m → Bool ↦ E (f2WordPolynomial w))
    (fun w : Fin l → Bool ↦ F (f2WordPolynomial w))

end OdlyzkoPoonen
