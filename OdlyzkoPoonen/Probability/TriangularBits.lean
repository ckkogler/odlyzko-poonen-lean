import OdlyzkoPoonen.Probability.PrescribedBits

/-!
# Triangular changes of Boolean coordinates

At coordinate `i`, the correction may depend arbitrarily on earlier bits, but
not on the current or later bits. Xoring with this correction is invertible:
the original bits can be recovered in order. This includes words of length zero.
-/

namespace OdlyzkoPoonen

/-- Each output of a correction rule depends only on strictly earlier bits. -/
def DependsOnEarlier {n : ℕ} (t : (Fin n → Bool) → Fin n → Bool) : Prop :=
  ∀ (i : Fin n) (v w : Fin n → Bool),
    (∀ j, j < i → v j = w j) → t v i = t w i

/-- Add a correction to each bit using Boolean xor. -/
def triangularBitMap {n : ℕ} (t : (Fin n → Bool) → Fin n → Bool)
    (w : Fin n → Bool) (i : Fin n) : Bool :=
  Bool.xor (w i) (t w i)

lemma triangularBitMap_injective {n : ℕ} {t : (Fin n → Bool) → Fin n → Bool}
    (ht : DependsOnEarlier t) : Function.Injective (triangularBitMap t) := by
  intro v w h
  have hp : ∀ k : ℕ, ∀ i : Fin n, i.val = k → v i = w i := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hik
      have he : t v i = t w i := ht i v w (fun j hj ↦
        ih j.val (by simpa only [← hik, Fin.lt_def] using hj) j rfl)
      have hx := congrFun h i
      change Bool.xor (v i) (t v i) = Bool.xor (w i) (t w i) at hx
      rw [he] at hx
      cases hv : v i <;> cases hw : w i <;> cases htwi : t w i <;>
        simp_all
  funext i
  exact hp i.val i rfl

lemma triangularBitMap_bijective {n : ℕ} {t : (Fin n → Bool) → Fin n → Bool}
    (ht : DependsOnEarlier t) : Function.Bijective (triangularBitMap t) := by
  have hi := triangularBitMap_injective ht
  exact ⟨hi, Finite.surjective_of_injective hi⟩

lemma uniformProbability_triangularBitMap {n : ℕ}
    {t : (Fin n → Bool) → Fin n → Bool} (ht : DependsOnEarlier t)
    (E : (Fin n → Bool) → Prop) :
    uniformProbability (fun w ↦ E (triangularBitMap t w)) = uniformProbability E :=
  uniformProbability_bijective (triangularBitMap_bijective ht) E

lemma uniformProbability_triangular_prescribedBits {n : ℕ}
    {t : (Fin n → Bool) → Fin n → Bool} (ht : DependsOnEarlier t)
    (s : Finset (Fin n)) (v : Fin n → Bool) :
    uniformProbability (fun w : Fin n → Bool ↦
      ∀ i ∈ s, triangularBitMap t w i = v i) = (1 / 2 : ℝ) ^ s.card :=
  (uniformProbability_triangularBitMap ht (fun z ↦ ∀ i ∈ s, z i = v i)).trans
    (uniformProbability_prescribedBits s v)

end OdlyzkoPoonen
