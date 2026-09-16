import OdlyzkoPoonen.Probability.UniformTransport

/-!
# Counting prescribed bits

A word with prescribed values on a set of coordinates is equivalent to a freely
chosen word on the complementary coordinates. Thus prescribing `k` bits in a
uniform Boolean word has probability exactly `2⁻ᵏ`, including an empty set of
constraints or an empty word.
-/

namespace OdlyzkoPoonen

/-- Restriction to unconstrained coordinates identifies a prescribed-bit fiber
with the full Boolean word space on its complement. -/
noncomputable def prescribedBitsEquiv {ι : Type*} (s : Finset ι) (v : ι → Bool) :
    {w : ι → Bool // ∀ i ∈ s, w i = v i} ≃ ({i : ι // i ∉ s} → Bool) := by
  classical
  refine {
    toFun := fun w i ↦ w.val i.val
    invFun := fun w ↦ ⟨fun i ↦ if hi : i ∈ s then v i else w ⟨i, hi⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · intro i hi
    exact dite_eq_left hi
  · intro w
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simpa only [dite_eq_left hi] using (w.property i hi).symm
    · simp only [dite_eq_right hi]
  · intro w
    funext i
    simp only [dite_eq_right i.property]

lemma card_prescribedBits {n : ℕ} (s : Finset (Fin n)) (v : Fin n → Bool) :
    Fintype.card {w : Fin n → Bool // ∀ i ∈ s, w i = v i} = 2 ^ (n - s.card) := by
  classical
  rw [Fintype.card_congr (prescribedBitsEquiv s v)]
  simp [Fintype.card_subtype_compl]

lemma uniformProbability_prescribedBits {n : ℕ} (s : Finset (Fin n))
    (v : Fin n → Bool) :
    uniformProbability (fun w : Fin n → Bool ↦ ∀ i ∈ s, w i = v i) =
      (1 / 2 : ℝ) ^ s.card := by
  classical
  have hs : s.card ≤ n := by simpa using Finset.card_le_univ s
  unfold uniformProbability
  rw [← Fintype.card_subtype, card_prescribedBits]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat]
  have hpow : (2 : ℝ) ^ n = 2 ^ (n - s.card) * 2 ^ s.card := by
    rw [← pow_add, Nat.sub_add_cancel hs]
  rw [hpow, one_div_pow]
  field_simp

end OdlyzkoPoonen
