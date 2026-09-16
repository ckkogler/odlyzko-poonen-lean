import OdlyzkoPoonen.Probability.BitWeights
import Mathlib.Data.Fintype.Powerset

/-!
# Exact counts of true bits in a uniform Boolean word

The true coordinates identify a Boolean word with a finite subset of its index
set. Subsets of size `k` are counted by `Nat.choose n k`, giving the actual
binomial probability in the established uniform word model. Out-of-range
counts and empty words are included in the same formula.
-/

namespace OdlyzkoPoonen
open scoped Classical

/-- A Boolean word is identified with its finite set of true coordinates. -/
noncomputable def booleanWordFinsetEquiv (n : ℕ) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun w := Finset.univ.filter (fun i ↦ w i = true)
  invFun s i := decide (i ∈ s)
  left_inv w := by
    funext i
    cases hi : w i <;> simp [hi]
  right_inv s := by
    ext i
    simp

lemma trueBitCount_eq_card (n : ℕ) (w : Fin n → Bool) :
    trueBitCount w = (booleanWordFinsetEquiv n w).card := rfl

lemma uniformProbability_trueBitCount (n k : ℕ) :
    uniformProbability (fun w : Fin n → Bool ↦ trueBitCount w = k) =
      (n.choose k : ℝ) / (2 : ℝ) ^ n := by
  classical
  simp_rw [trueBitCount_eq_card]
  rw [uniformProbability_equiv (booleanWordFinsetEquiv n)
    (fun s : Finset (Fin n) ↦ s.card = k)]
  unfold uniformProbability
  rw [← Fintype.card_subtype, Fintype.card_finset_len]
  simp only [Fintype.card_fin, Fintype.card_finset,
    Nat.cast_pow, Nat.cast_ofNat]

lemma uniformProbability_trueBitCount_eq_zero {n k : ℕ} (h : n < k) :
    uniformProbability (fun w : Fin n → Bool ↦ trueBitCount w = k) = 0 := by
  rw [uniformProbability_trueBitCount, Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_div]

end OdlyzkoPoonen
