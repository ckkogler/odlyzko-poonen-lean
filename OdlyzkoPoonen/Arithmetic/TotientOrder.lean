import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic

/-!
# An elementary bound on cyclotomic orders

The order of a cyclotomic polynomial is at most twice the square of its degree.
We prove the stronger odd-integer bound simultaneously. Multiplicativity then
loses a factor of two only once, since coprime factors cannot both be even.
This coarse bound suffices for the later probability union over all orders.
-/

namespace OdlyzkoPoonen

lemma coprime_odd_or_odd {a b : ℕ} (h : a.Coprime b) : Odd a ∨ Odd b := by
  by_cases ha : Odd a
  · exact Or.inl ha
  · right
    have he : 2 ∣ a := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp ha)
    exact (h.of_dvd_left he).odd_of_left

lemma order_le_totient_sq_with_odd (n : ℕ) :
    n ≤ 2 * n.totient ^ 2 ∧ (Odd n → n ≤ n.totient ^ 2) := by
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
  · simp
  · intro p e hp
    cases e with
    | zero => simp
    | succ e =>
      rw [Nat.totient_prime_pow_succ hp]
      have hx : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
      by_cases hp2 : p = 2
      · subst p
        simp only [Nat.reduceSub, mul_one, pow_succ]
        constructor
        · nlinarith
        · intro ho
          have ht := Nat.odd_mul.mp ho
          norm_num at ht
      · have hp3 : 3 ≤ p := by have := hp.two_le; omega
        have hs : p ≤ (p - 1) ^ 2 := by
          have he : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
          nlinarith
        have hx2 : p ^ e ≤ (p ^ e) ^ 2 := by nlinarith
        have hstrong : p ^ (e + 1) ≤ (p ^ e * (p - 1)) ^ 2 := by
          rw [pow_succ, mul_pow]
          exact Nat.mul_le_mul hx2 hs
        exact ⟨by omega, fun _ ↦ hstrong⟩
  · intro a b _ _ hab ha hb
    rw [Nat.totient_mul hab, mul_pow]
    constructor
    · rcases coprime_odd_or_odd hab with hoa | hob
      · have h := Nat.mul_le_mul (ha.2 hoa) hb.1
        nlinarith
      · have h := Nat.mul_le_mul ha.1 (hb.2 hob)
        nlinarith
    · intro ho
      exact Nat.mul_le_mul (ha.2 (Nat.odd_mul.mp ho).1) (hb.2 (Nat.odd_mul.mp ho).2)

lemma order_le_two_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 :=
  (order_le_totient_sq_with_odd n).1

lemma odd_order_le_totient_sq {n : ℕ} (hn : Odd n) : n ≤ n.totient ^ 2 :=
  (order_le_totient_sq_with_odd n).2 hn

end OdlyzkoPoonen
