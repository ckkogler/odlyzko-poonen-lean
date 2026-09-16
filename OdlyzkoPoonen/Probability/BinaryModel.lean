import OdlyzkoPoonen.Polynomial.BinaryWords
import OdlyzkoPoonen.Probability.FiniteUniform

/-!
# Uniform binary-polynomial model

A degree-`m + 1` polynomial is sampled by taking a uniform word of `m` bits.
The polynomial map is injective and exhausts the exact endpoint family, so its
pushforward probabilities equal uniform counts on that family.
-/

open scoped Classical

namespace OdlyzkoPoonen

/-- Probability of a polynomial event when its `m` internal bits are uniform. -/
noncomputable def binaryProbability (m : ℕ) (E : Polynomial ℤ → Prop) : ℝ :=
  uniformProbability (fun w : Fin m → Bool ↦ E (wordPolynomial w))

lemma binaryProbability_eq_count (m : ℕ) (E : Polynomial ℤ → Prop) :
    binaryProbability m E = ((binaryFamily m).filter E).card / (2 : ℝ) ^ m := by
  classical
  have h : (Finset.univ.filter (fun w : Fin m → Bool ↦ E (wordPolynomial w))).image
      wordPolynomial = (binaryFamily m).filter E := by
    ext p
    simp only [binaryFamily, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, rfl⟩, hw⟩
    · rintro ⟨⟨w, rfl⟩, hw⟩
      exact ⟨w, hw, rfl⟩
  rw [binaryProbability, uniformProbability, ← h,
    Finset.card_image_of_injective _ wordPolynomial_injective]
  simp

lemma binaryProbability_endpoints (m : ℕ) :
    binaryProbability m (HasBinaryEndpoints (m + 1)) = 1 := by
  unfold binaryProbability
  have h : (fun w : Fin m → Bool ↦ HasBinaryEndpoints (m + 1) (wordPolynomial w)) =
      (fun _ ↦ True) := by
    funext w
    exact propext ⟨fun _ ↦ trivial, fun _ ↦ wordPolynomial_endpoints w⟩
  rw [h, uniformProbability_true]

end OdlyzkoPoonen
