import OdlyzkoPoonen.Asymptotics.SharpCyclotomicTruncation

/-!
# The four cyclotomic events relevant above order two

Only orders 2, 3, 4 and 6 remain when the error tolerance is `O(n⁻²)`.
The order-one event is impossible because all coefficients are nonnegative
and the constant coefficient is one.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics
open scoped Classical

lemma positive_totient_lt_four_iff {k : ℕ} (hk : 0 < k) :
    k.totient < 4 ↔ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6 := by
  constructor
  · intro ht
    have hb : k ≤ 18 := by
      calc
        k ≤ 2 * k.totient ^ 2 := order_le_two_totient_sq k
        _ ≤ 2 * 3 ^ 2 := by gcongr; omega
        _ = 18 := by norm_num
    have hsmall : ∀ j : Fin 19, 0 < j.val → j.val.totient < 4 →
        j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 6 := by decide
    exact hsmall ⟨k, by omega⟩ hk ht
  · rintro (rfl | rfl | rfl | rfl | rfl) <;> decide

lemma HasBinaryEndpoints.bounded_cyclotomic_four_iff {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) :
    HasBoundedDegreeCyclotomicDivisor 4 p ↔
      cyclotomic 2 ℤ ∣ p ∨ cyclotomic 3 ℤ ∣ p ∨
        cyclotomic 4 ℤ ∣ p ∨ cyclotomic 6 ℤ ∣ p := by
  constructor
  · rintro ⟨k, hk, ht, hd⟩
    rcases (positive_totient_lt_four_iff hk).mp ht with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (hp.not_cyclotomic_one_dvd hd)
    · exact Or.inl hd
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr (Or.inl hd))
    · exact Or.inr (Or.inr (Or.inr hd))
  · rintro (h | h | h | h)
    · exact ⟨2, by decide, by decide, h⟩
    · exact ⟨3, by decide, by decide, h⟩
    · exact ⟨4, by decide, by decide, h⟩
    · exact ⟨6, by decide, by decide, h⟩

/-- Reducibility is approximated by four fixed events with quadratic error. -/
theorem binaryProbability_reducible_four_cyclotomic_approximation :
    (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (fun p ↦ cyclotomic 2 ℤ ∣ p ∨
        cyclotomic 3 ℤ ∣ p ∨ cyclotomic 4 ℤ ∣ p ∨ cyclotomic 6 ℤ ∣ p))
      =O[atTop] (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by
  have he (n : ℕ) : binaryProbability (n - 1) (HasBoundedDegreeCyclotomicDivisor 4) =
      binaryProbability (n - 1) (fun p ↦ cyclotomic 2 ℤ ∣ p ∨
        cyclotomic 3 ℤ ∣ p ∨ cyclotomic 4 ℤ ∣ p ∨ cyclotomic 6 ℤ ∣ p) := by
    unfold binaryProbability
    congr 1
    funext w
    exact propext (wordPolynomial_endpoints w).bounded_cyclotomic_four_iff
  simpa only [show 2 * 2 = 4 by rfl, he] using
    binaryProbability_reducible_sharp_finite_cyclotomic_approximation 2 (by omega)

end OdlyzkoPoonen
