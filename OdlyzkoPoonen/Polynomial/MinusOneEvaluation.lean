import OdlyzkoPoonen.Polynomial.BinaryWords
import OdlyzkoPoonen.Probability.BernoulliCount

/-!
# Evaluation at minus one as a count of complemented bits

Internal word index `i` corresponds to polynomial exponent `i+1`. Complementing
exactly the odd indices changes the alternating coefficient sum into an ordinary
count of true bits. The number of complemented coordinates is `m/2`. All
identities hold for an empty word as well.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

/-- Complement the coefficients that carry a positive sign at minus one. -/
def alternatingComplement {m : ℕ} (w : Fin m → Bool) (i : Fin m) : Bool :=
  if i.val % 2 = 1 then !(w i) else w i

lemma alternatingComplement_involutive (m : ℕ) :
    Function.Involutive (@alternatingComplement m) := by
  intro w
  funext i
  simp only [alternatingComplement]
  split_ifs <;> simp

lemma alternatingComplement_bijective (m : ℕ) :
    Function.Bijective (@alternatingComplement m) :=
  (alternatingComplement_involutive m).bijective

lemma sum_bitValue_eq_trueBitCount {m : ℕ} (w : Fin m → Bool) :
    (∑ i, bitValue (w i)) = (trueBitCount w : ℤ) := by
  simp [bitValue, trueBitCount]

lemma sum_odd_position_indicators (m : ℕ) :
    (∑ i ∈ Finset.range m, if i % 2 = 1 then (1 : ℤ) else 0) = (m / 2 : ℕ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

lemma signed_bitValue (i : ℕ) (b : Bool) :
    bitValue b * (-1 : ℤ) ^ (i + 1) =
      (if i % 2 = 1 then 1 else 0) -
        bitValue (if i % 2 = 1 then !b else b) := by
  rw [neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi
  · have he : (i + 1) % 2 = 1 := by omega
    cases b <;> simp [hi, he, bitValue]
  · have he : (i + 1) % 2 = 0 := by omega
    cases b <;> simp [hi, he, bitValue]

lemma eval_wordPolynomial_minus_one {m : ℕ} (w : Fin m → Bool) :
    (wordPolynomial w).eval (-1) =
      1 + (-1 : ℤ) ^ (m + 1) + (m / 2 : ℕ) -
        (trueBitCount (alternatingComplement w) : ℤ) := by
  have hs : (∑ i : Fin m, bitValue (w i) * (-1 : ℤ) ^ (i.val + 1)) =
      (m / 2 : ℕ) - (trueBitCount (alternatingComplement w) : ℤ) := by
    simp_rw [signed_bitValue]
    rw [Finset.sum_sub_distrib]
    change (∑ i : Fin m, if i.val % 2 = 1 then (1 : ℤ) else 0) -
      (∑ i : Fin m, bitValue (alternatingComplement w i)) = _
    rw [sum_bitValue_eq_trueBitCount,
      Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ if i % 2 = 1 then (1 : ℤ) else 0) m,
      sum_odd_position_indicators]
  simp only [wordPolynomial, interiorPolynomial, eval_add, eval_one, eval_finsetSum,
    eval_mul, eval_C, eval_pow, eval_X]
  rw [hs]
  ring

end OdlyzkoPoonen
