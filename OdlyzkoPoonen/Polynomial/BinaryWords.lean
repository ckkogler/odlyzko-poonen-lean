import OdlyzkoPoonen.Polynomial.Binary

/-!
# From a finite binary word to its polynomial

A word with `m` internal bits gives a degree-`m + 1` polynomial. Its two endpoint
coefficients are fixed at one. This degree convention includes degree one using
an empty word and avoids artificial choices for negative word lengths.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

/-- A bit interpreted as an integer zero or one. -/
def bitValue (b : Bool) : ℤ := if b then 1 else 0

lemma bitValue_binary (b : Bool) : bitValue b = 0 ∨ bitValue b = 1 := by
  cases b <;> simp [bitValue]

lemma bitValue_injective : Function.Injective bitValue := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitValue]

/-- Internal coefficients, occupying positions one through `m`. -/
noncomputable def interiorPolynomial {m : ℕ} (w : Fin m → Bool) : ℤ[X] :=
  ∑ i : Fin m, C (bitValue (w i)) * X ^ (i.val + 1)

lemma coeff_interiorPolynomial {m : ℕ} (w : Fin m → Bool) (i : Fin m) :
    (interiorPolynomial w).coeff (i.val + 1) = bitValue (w i) := by
  classical
  simp only [interiorPolynomial, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hji : j.val + 1 ≠ i.val + 1 := by
      intro h
      exact hj (Fin.ext (by omega))
    have hij : i.val ≠ j.val := by intro h; exact hj (Fin.ext h.symm)
    simp [hij]
  · simp

lemma coeff_interiorPolynomial_outside {m : ℕ} (w : Fin m → Bool) (k : ℕ)
    (hk : k = 0 ∨ m < k) : (interiorPolynomial w).coeff k = 0 := by
  classical
  simp only [interiorPolynomial, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  apply Finset.sum_eq_zero
  intro i _
  have hi : i.val + 1 ≠ k := by
    have := i.isLt
    rcases hk with hk | hk <;> omega
  simp [Ne.symm hi]

/-- The actual binary polynomial with the given internal coefficient word. -/
noncomputable def wordPolynomial {m : ℕ} (w : Fin m → Bool) : ℤ[X] :=
  1 + interiorPolynomial w + X ^ (m + 1)

lemma coeff_wordPolynomial_zero {m : ℕ} (w : Fin m → Bool) :
    (wordPolynomial w).coeff 0 = 1 := by
  simp [wordPolynomial, Polynomial.coeff_one, coeff_interiorPolynomial_outside w 0 (Or.inl rfl)]

lemma coeff_wordPolynomial_top {m : ℕ} (w : Fin m → Bool) :
    (wordPolynomial w).coeff (m + 1) = 1 := by
  simp [wordPolynomial, Polynomial.coeff_one, coeff_interiorPolynomial_outside w (m + 1) (Or.inr (by omega))]

lemma coeff_wordPolynomial_internal {m : ℕ} (w : Fin m → Bool) (i : Fin m) :
    (wordPolynomial w).coeff (i.val + 1) = bitValue (w i) := by
  have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
  simp [wordPolynomial, Polynomial.coeff_one, coeff_interiorPolynomial, hi]

lemma coeff_wordPolynomial_above {m : ℕ} (w : Fin m → Bool) {k : ℕ}
    (hk : m + 1 < k) : (wordPolynomial w).coeff k = 0 := by
  have hk0 : k ≠ 0 := by omega
  have hkm : m + 1 ≠ k := by omega
  simp [wordPolynomial, Polynomial.coeff_one, coeff_interiorPolynomial_outside w k (Or.inr (by omega)), hk0, Ne.symm hkm]

lemma wordPolynomial_injective {m : ℕ} : Function.Injective (@wordPolynomial m) := by
  intro v w h
  funext i
  apply bitValue_injective
  have hc := congrArg (fun p : ℤ[X] ↦ p.coeff (i.val + 1)) h
  simpa only [coeff_wordPolynomial_internal] using hc


lemma natDegree_wordPolynomial {m : ℕ} (w : Fin m → Bool) :
    (wordPolynomial w).natDegree = m + 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      (fun k hk ↦ coeff_wordPolynomial_above w hk)
  · rw [coeff_wordPolynomial_top]
    norm_num

lemma wordPolynomial_endpoints {m : ℕ} (w : Fin m → Bool) :
    HasBinaryEndpoints (m + 1) (wordPolynomial w) := by
  refine ⟨?_, natDegree_wordPolynomial w, coeff_wordPolynomial_zero w, ?_⟩
  · change (wordPolynomial w).coeff (wordPolynomial w).natDegree = 1
    rw [natDegree_wordPolynomial, coeff_wordPolynomial_top]
  · intro k
    by_cases hk0 : k = 0
    · exact Or.inr (by rw [hk0, coeff_wordPolynomial_zero])
    by_cases hkt : k = m + 1
    · exact Or.inr (by rw [hkt, coeff_wordPolynomial_top])
    by_cases hk : k < m + 1
    · let i : Fin m := ⟨k - 1, by omega⟩
      have hi : i.val + 1 = k := by dsimp [i]; omega
      rw [← hi, coeff_wordPolynomial_internal]
      exact bitValue_binary _
    · exact Or.inl (coeff_wordPolynomial_above w (by omega))

lemma exists_wordPolynomial_eq {m : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints (m + 1) p) : ∃ w : Fin m → Bool, wordPolynomial w = p := by
  classical
  let w : Fin m → Bool := fun i ↦ decide (p.coeff (i.val + 1) = 1)
  have hw (i : Fin m) : bitValue (w i) = p.coeff (i.val + 1) := by
    rcases hp.binary (i.val + 1) with h | h <;> simp [w, bitValue, h]
  refine ⟨w, ?_⟩
  ext k
  by_cases hk0 : k = 0
  · rw [hk0, coeff_wordPolynomial_zero, hp.constant]
  by_cases hkt : k = m + 1
  · rw [hkt, coeff_wordPolynomial_top, hp.coeff_degree]
  by_cases hk : k < m + 1
  · let i : Fin m := ⟨k - 1, by omega⟩
    have hi : i.val + 1 = k := by dsimp [i]; omega
    rw [← hi, coeff_wordPolynomial_internal, hw]
  · rw [coeff_wordPolynomial_above w (by omega), hp.coeff_eq_zero_above (by omega)]

/-- The actual finite set of degree-`m + 1` endpoint-fixed binary polynomials. -/
noncomputable def binaryFamily (m : ℕ) : Finset ℤ[X] :=
  Finset.univ.image (@wordPolynomial m)

lemma mem_binaryFamily_iff {m : ℕ} {p : ℤ[X]} :
    p ∈ binaryFamily m ↔ HasBinaryEndpoints (m + 1) p := by
  classical
  constructor
  · intro h
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp h
    exact wordPolynomial_endpoints w
  · intro hp
    obtain ⟨w, rfl⟩ := exists_wordPolynomial_eq hp
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩

lemma card_binaryFamily (m : ℕ) : (binaryFamily m).card = 2 ^ m := by
  classical
  rw [binaryFamily, Finset.card_image_of_injective _ wordPolynomial_injective]
  simp

end OdlyzkoPoonen
