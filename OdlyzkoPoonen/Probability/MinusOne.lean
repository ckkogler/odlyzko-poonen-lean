import OdlyzkoPoonen.Polynomial.MinusOneEvaluation
import OdlyzkoPoonen.Probability.BinaryModel

/-!
# Exact probabilities of a root at minus one

The degree is one more than the number of internal bits. Thus `2*r` internal
bits give the odd-degree formula, and `2*r-1` give the even-degree formula.
The latter requires `r ≥ 1`; the former includes degree one (`r = 0`).
The binomial coefficient uses its usual natural-number convention, which is
zero beyond the upper index. In particular the degree-two probability is zero.
-/

namespace OdlyzkoPoonen

lemma uniformProbability_alternatingComplement {m : ℕ}
    (E : (Fin m → Bool) → Prop) :
    uniformProbability (fun w ↦ E (alternatingComplement w)) = uniformProbability E :=
  uniformProbability_bijective (alternatingComplement_bijective m) E

lemma eval_wordPolynomial_minus_one_odd (r : ℕ) (w : Fin (2 * r) → Bool) :
    (wordPolynomial w).eval (-1) =
      (r : ℤ) - (trueBitCount (alternatingComplement w) : ℤ) := by
  have hd : 2 * r / 2 = r := by omega
  have hp : (-1 : ℤ) ^ (2 * r + 1) = -1 := by
    rw [neg_one_pow_eq_pow_mod_two]
    have h : (2 * r + 1) % 2 = 1 := by omega
    rw [h, pow_one]
  rw [eval_wordPolynomial_minus_one, hd, hp]
  ring

lemma eval_wordPolynomial_minus_one_even {r : ℕ} (hr : 1 ≤ r)
    (w : Fin (2 * r - 1) → Bool) :
    (wordPolynomial w).eval (-1) =
      (r + 1 : ℤ) - (trueBitCount (alternatingComplement w) : ℤ) := by
  have hd : (2 * r - 1) / 2 = r - 1 := by omega
  have he : 2 * r - 1 + 1 = 2 * r := by omega
  have hp : (-1 : ℤ) ^ (2 * r) = 1 := by
    rw [neg_one_pow_eq_pow_mod_two]
    have h : (2 * r) % 2 = 0 := by omega
    rw [h, pow_zero]
  rw [eval_wordPolynomial_minus_one, he, hd, hp]
  have hcast : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
  rw [hcast]
  ring

/-- For degree `2*r+1`, the exact probability of a root at minus one. -/
theorem binaryProbability_minus_one_odd (r : ℕ) :
    binaryProbability (2 * r) (fun p ↦ p.eval (-1) = 0) =
      ((2 * r).choose r : ℝ) / (2 : ℝ) ^ (2 * r) := by
  unfold binaryProbability
  have he : (fun w : Fin (2 * r) → Bool ↦ (wordPolynomial w).eval (-1) = 0) =
      (fun w ↦ trueBitCount (alternatingComplement w) = r) := by
    funext w
    apply propext
    rw [eval_wordPolynomial_minus_one_odd]
    omega
  rw [he, uniformProbability_alternatingComplement
    (fun w : Fin (2 * r) → Bool ↦ trueBitCount w = r), uniformProbability_trueBitCount]

/-- For degree `2*r`, including degree two and its out-of-range binomial index. -/
theorem binaryProbability_minus_one_even {r : ℕ} (hr : 1 ≤ r) :
    binaryProbability (2 * r - 1) (fun p ↦ p.eval (-1) = 0) =
      ((2 * r - 1).choose (r + 1) : ℝ) / (2 : ℝ) ^ (2 * r - 1) := by
  unfold binaryProbability
  have he : (fun w : Fin (2 * r - 1) → Bool ↦ (wordPolynomial w).eval (-1) = 0) =
      (fun w ↦ trueBitCount (alternatingComplement w) = r + 1) := by
    funext w
    apply propext
    rw [eval_wordPolynomial_minus_one_even hr]
    omega
  rw [he, uniformProbability_alternatingComplement
    (fun w : Fin (2 * r - 1) → Bool ↦ trueBitCount w = r + 1),
    uniformProbability_trueBitCount]

lemma binaryProbability_minus_one_degree_one :
    binaryProbability 0 (fun p ↦ p.eval (-1) = 0) = 1 := by
  simpa using binaryProbability_minus_one_odd 0

lemma binaryProbability_minus_one_degree_two :
    binaryProbability 1 (fun p ↦ p.eval (-1) = 0) = 0 := by
  simpa using binaryProbability_minus_one_even (r := 1) (by omega)

end OdlyzkoPoonen
