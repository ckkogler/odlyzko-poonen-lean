import OdlyzkoPoonen.Reducibility.CyclotomicRemainder
import OdlyzkoPoonen.Probability.CompanionLogarithmicBound
import OdlyzkoPoonen.Probability.EventComplement
import OdlyzkoPoonen.Probability.FiniteEvents

/-!
# A finite degree cutoff for the cyclotomic part

The failure probability is bounded by the sum of the companion event, the
noncyclotomic reciprocal-divisor event, and the reciprocal degree tail.
All constants are independent of both the ambient degree and the cutoff.
-/

namespace OdlyzkoPoonen

lemma cyclotomic_cutoff_failure_probability_le {n L : ℕ} (hn : 1 ≤ n) (hL : L ≤ n) :
    binaryProbability (n - 1) (fun P ↦ ¬ HasIrreducibleNoncyclotomicPartBelow L P) ≤
      binaryProbability (n - 1) (HasModFourCompanion n) +
        binaryProbability (n - 1) HasNoncyclotomicReciprocalDivisor +
          8 * (2 : ℝ) ^ (-(L : ℝ) / 2) := by
  have htail := binaryProbability_large_reciprocal_divisor_le hn L
  have hmono : binaryProbability (n - 1) (fun P ↦ ¬ HasIrreducibleNoncyclotomicPartBelow L P) ≤
      binaryProbability (n - 1) (fun P ↦ (HasModFourCompanion n P ∨
        HasNoncyclotomicReciprocalDivisor P) ∨ HasLargeReciprocalIntegerDivisor L P) := by
    apply uniformProbability_mono
    intro w hw
    by_contra h
    push Not at h
    have hp := wordPolynomial_endpoints w
    rw [Nat.sub_add_cancel hn] at hp
    exact hw (hp.irreducibleNoncyclotomicPartBelow hL h.1.1 h.1.2 h.2)
  refine hmono.trans ?_
  have h₁ := binaryProbability_or_le_add (n - 1)
    (fun P ↦ HasModFourCompanion n P ∨ HasNoncyclotomicReciprocalDivisor P)
    (HasLargeReciprocalIntegerDivisor L)
  have h₂ := binaryProbability_or_le_add (n - 1)
    (HasModFourCompanion n) HasNoncyclotomicReciprocalDivisor
  have hpos : 0 ≤ (2 : ℝ) ^ (-(L : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  linarith

theorem cyclotomic_irreducible_factorization_cutoff_probability :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n L : ℕ, 3 ≤ n → 1 ≤ L → L ≤ n →
      1 - C * Real.exp (-c * n / Real.log (n : ℝ) ^ 4) -
        8 * (2 : ℝ) ^ (-(L : ℝ) / 2) ≤
          binaryProbability (n - 1) (HasIrreducibleNoncyclotomicPartBelow L) := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hrec⟩ := noncyclotomic_reciprocal_divisor_probability
  obtain ⟨C₁, hC₁, hcomp⟩ := mod_four_companion_logarithmic_exponential_bound
  let c := min c₀ (1 / 32 : ℝ)
  have hc : 0 < c := lt_min hc₀ (by norm_num)
  refine ⟨c, C₀ + C₁, hc, by positivity, ?_⟩
  intro n L hn _ hL
  have h₀ := (hrec n hn).trans (mul_le_mul_of_nonneg_left
    (logarithmic_exp_antitone_rate (min_le_left c₀ (1 / 32)) n) hC₀.le)
  have h₁ := (hcomp n hn).trans (mul_le_mul_of_nonneg_left
    (logarithmic_exp_antitone_rate (min_le_right c₀ (1 / 32)) n) hC₁.le)
  have hfail := cyclotomic_cutoff_failure_probability_le (by omega : 1 ≤ n) hL
  have hcompl := uniformProbability_not (fun w : Fin (n - 1) → Bool ↦
    HasIrreducibleNoncyclotomicPartBelow L (wordPolynomial w))
  change binaryProbability (n - 1) (fun P ↦ ¬ HasIrreducibleNoncyclotomicPartBelow L P) =
    1 - binaryProbability (n - 1) (HasIrreducibleNoncyclotomicPartBelow L) at hcompl
  change _ ≤ C₀ * Real.exp (-c * n / Real.log (n : ℝ) ^ 4) at h₀
  change _ ≤ C₁ * Real.exp (-c * n / Real.log (n : ℝ) ^ 4) at h₁
  nlinarith

end OdlyzkoPoonen
