import OdlyzkoPoonen.Reducibility.FactorAlternative
import OdlyzkoPoonen.Polynomial.IntegerRoots
import OdlyzkoPoonen.Polynomial.CyclotomicDivisors
import OdlyzkoPoonen.Probability.FiniteEvents
import OdlyzkoPoonen.ModFour.CompanionProbability

/-!
# Probability reductions for rational reducibility

The excess over the minus-one-root event is nonnegative and equals an actual
set difference. Cyclotomic classification and factor reversal bound that excess
by the companion event, reciprocal divisors without any cyclotomic divisor of
the original polynomial, and the higher cyclotomic event. The latter two events
still require their arithmetic probability estimates.
-/

namespace OdlyzkoPoonen

lemma reducible_without_cyclotomic_probability_le {n : ℕ} (hn : 1 ≤ n) :
    binaryProbability (n - 1) (fun p ↦ ReducibleOverRat p ∧ ¬ HasCyclotomicDivisor p) ≤
      binaryProbability (n - 1) (HasModFourCompanion n) +
        binaryProbability (n - 1) (fun p ↦
          HasLargeReciprocalIntegerDivisor 1 p ∧ ¬ HasCyclotomicDivisor p) := by
  calc
    _ ≤ binaryProbability (n - 1) (fun p ↦ HasModFourCompanion n p ∨
        (HasLargeReciprocalIntegerDivisor 1 p ∧ ¬ HasCyclotomicDivisor p)) := by
      apply uniformProbability_mono
      intro w hw
      have hp := wordPolynomial_endpoints w
      rw [Nat.sub_add_cancel hn] at hp
      rcases hp.companion_or_reciprocal_of_reducible hn hw.1 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hw.2⟩
    _ ≤ _ := binaryProbability_or_le_add _ _ _

lemma reducible_sub_minus_one_probability_eq {n : ℕ} (hn : 2 ≤ n) :
    binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) =
        binaryProbability (n - 1) (fun p ↦ ReducibleOverRat p ∧ p.eval (-1) ≠ 0) := by
  apply uniformProbability_sub_of_imp
  intro w hw
  have hp := wordPolynomial_endpoints w
  rw [Nat.sub_add_cancel (show 1 ≤ n by omega)] at hp
  exact hp.reducible_of_minus_one hn hw

lemma reducible_sub_minus_one_probability_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) := by
  rw [reducible_sub_minus_one_probability_eq hn]
  exact uniformProbability_nonneg _

lemma reducible_sub_minus_one_probability_le {n : ℕ} (hn : 2 ≤ n) :
    binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) ≤
        binaryProbability (n - 1) (fun p ↦ ReducibleOverRat p ∧ ¬ HasCyclotomicDivisor p) +
          binaryProbability (n - 1) HasHigherCyclotomicDivisor := by
  rw [reducible_sub_minus_one_probability_eq hn]
  calc
    _ ≤ binaryProbability (n - 1) (fun p ↦
        (ReducibleOverRat p ∧ ¬ HasCyclotomicDivisor p) ∨ HasHigherCyclotomicDivisor p) := by
      apply uniformProbability_mono
      intro w hw
      have hp := wordPolynomial_endpoints w
      rw [Nat.sub_add_cancel (show 1 ≤ n by omega)] at hp
      by_cases hc : HasCyclotomicDivisor (wordPolynomial w)
      · rcases hp.cyclotomic_alternative hc with h | h
        · exact Or.inr h
        · exact False.elim (hw.2 h)
      · exact Or.inl ⟨hw.1, hc⟩
    _ ≤ _ := binaryProbability_or_le_add _ _ _

/-- The full finite-degree reduction, with only the two arithmetic events left. -/
lemma reducible_probability_reduction {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ binaryProbability (n - 1) ReducibleOverRat -
        binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) ∧
      binaryProbability (n - 1) ReducibleOverRat -
        binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) ≤
          8 * (3 / 4 : ℝ) ^ ((n - 1) / 4) +
            binaryProbability (n - 1) (fun p ↦
              HasLargeReciprocalIntegerDivisor 1 p ∧ ¬ HasCyclotomicDivisor p) +
            binaryProbability (n - 1) HasHigherCyclotomicDivisor := by
  refine ⟨reducible_sub_minus_one_probability_nonneg hn, ?_⟩
  have h₁ := reducible_sub_minus_one_probability_le hn
  have h₂ := reducible_without_cyclotomic_probability_le (show 1 ≤ n by omega)
  have h₃ := mod_four_companion_probability_le n (by omega)
  linarith

end OdlyzkoPoonen
