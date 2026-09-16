import OdlyzkoPoonen.Probability.TriangularBits

/-!
# Constraints controlled by fresh fair bits

Suppose the `i`th output depends only on input coordinates through `i`. On an
active set of coordinates, toggling the current input toggles that output. The
active outputs, together with the inactive inputs, form a triangular bijection.
Consequently prescribed active outputs have probability exactly `2⁻ᵏ`, and
requiring all outputs to vanish has probability at most that quantity.
-/

namespace OdlyzkoPoonen

/-- Each output is determined by input coordinates through its own index. -/
def DependsOnPrefix {n : ℕ} (D : (Fin n → Bool) → Fin n → Bool) : Prop :=
  ∀ (i : Fin n) (v w : Fin n → Bool),
    (∀ j, j ≤ i → v j = w j) → D v i = D w i

/-- The current bit toggles the current output at every active coordinate. -/
def TogglesOn {n : ℕ} (s : Finset (Fin n))
    (D : (Fin n → Bool) → Fin n → Bool) : Prop :=
  ∀ i ∈ s, ∀ w, D (Function.update w i (!(w i))) i = !(D w i)

/-- The correction that turns active input bits into outputs and leaves the
inactive input bits unchanged. -/
def freshBitCorrection {n : ℕ} (s : Finset (Fin n))
    (D : (Fin n → Bool) → Fin n → Bool) (w : Fin n → Bool) (i : Fin n) : Bool :=
  if i ∈ s then Bool.xor (w i) (D w i) else false

lemma freshBitCorrection_dependsOnEarlier {n : ℕ} {s : Finset (Fin n)}
    {D : (Fin n → Bool) → Fin n → Bool} (hp : DependsOnPrefix D)
    (hf : TogglesOn s D) : DependsOnEarlier (freshBitCorrection s D) := by
  intro i v w hprev
  by_cases hi : i ∈ s
  · simp only [freshBitCorrection, ite_eq_left hi]
    by_cases he : v i = w i
    · have hd : D v i = D w i := hp i v w (by
        intro j hj
        rcases lt_or_eq_of_le hj with hj | rfl
        · exact hprev j hj
        · exact he)
      rw [he, hd]
    · have hwi : w i = !(v i) := by
        cases hv : v i <;> cases hw : w i <;> simp_all
      have hu : D (Function.update v i (w i)) i = D w i := hp i _ w (by
        intro j hj
        by_cases hji : j = i
        · subst j
          simp
        · rw [Function.update_of_ne hji]
          exact hprev j (lt_of_le_of_ne hj hji))
      rw [hwi, hf i hi v] at hu
      rw [hwi, ← hu]
      cases v i <;> cases D v i <;> rfl
  · simp only [freshBitCorrection, ite_eq_right hi]

lemma triangular_freshBitCorrection_active {n : ℕ} {s : Finset (Fin n)}
    (D : (Fin n → Bool) → Fin n → Bool) (w : Fin n → Bool)
    {i : Fin n} (hi : i ∈ s) :
    triangularBitMap (freshBitCorrection s D) w i = D w i := by
  simp only [triangularBitMap, freshBitCorrection, ite_eq_left hi]
  cases w i <;> cases D w i <;> rfl

lemma triangular_freshBitCorrection_inactive {n : ℕ} {s : Finset (Fin n)}
    (D : (Fin n → Bool) → Fin n → Bool) (w : Fin n → Bool)
    {i : Fin n} (hi : i ∉ s) :
    triangularBitMap (freshBitCorrection s D) w i = w i := by
  simp [triangularBitMap, freshBitCorrection, hi]

lemma uniformProbability_freshBitConstraints {n : ℕ} {s : Finset (Fin n)}
    {D : (Fin n → Bool) → Fin n → Bool} (hp : DependsOnPrefix D)
    (hf : TogglesOn s D) (v : Fin n → Bool) :
    uniformProbability (fun w : Fin n → Bool ↦ ∀ i ∈ s, D w i = v i) =
      (1 / 2 : ℝ) ^ s.card := by
  have he : (fun w : Fin n → Bool ↦ ∀ i ∈ s,
      triangularBitMap (freshBitCorrection s D) w i = v i) =
      (fun w ↦ ∀ i ∈ s, D w i = v i) := by
    funext w
    apply propext
    exact forall_congr' (fun i ↦ forall_congr' (fun hi ↦ by
      rw [triangular_freshBitCorrection_active D w hi]))
  rw [← he]
  exact uniformProbability_triangular_prescribedBits
    (freshBitCorrection_dependsOnEarlier hp hf) s v

lemma uniformProbability_all_outputs_zero_le {n : ℕ} {s : Finset (Fin n)}
    {D : (Fin n → Bool) → Fin n → Bool} (hp : DependsOnPrefix D)
    (hf : TogglesOn s D) :
    uniformProbability (fun w : Fin n → Bool ↦ ∀ i, D w i = false) ≤
      (1 / 2 : ℝ) ^ s.card := by
  calc
    _ ≤ uniformProbability (fun w : Fin n → Bool ↦ ∀ i ∈ s, D w i = false) :=
      uniformProbability_mono (fun _ h i _ ↦ h i)
    _ = _ := uniformProbability_freshBitConstraints hp hf (fun _ ↦ false)

end OdlyzkoPoonen
