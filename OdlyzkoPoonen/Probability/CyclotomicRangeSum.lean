import OdlyzkoPoonen.Probability.CyclotomicIntermediateDegree
import OdlyzkoPoonen.Probability.FiniteEvents

/-!
# A finite quantitative bound for every higher cyclotomic divisor

The higher-degree event is covered by degree two, degrees from three to a
cutoff, and degrees at least the cutoff. The cover holds for every cutoff,
including the cases where some ranges are empty. All orders are included.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma binaryProbability_higher_cyclotomic_range_sum {n L : ℕ} (hn : 1 ≤ n)
    (hsmall : 8 * (L : ℝ) / Real.sqrt (n : ℝ) ≤ 1) :
    binaryProbability (n - 1) HasHigherCyclotomicDivisor ≤
      1024 / (n : ℝ) + 1024 * (L : ℝ) ^ 5 / ((n : ℝ) * Real.sqrt (n : ℝ)) +
        4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ L := by
  let E₂ := fun p : ℤ[X] ↦ ∃ k, k.totient = 2 ∧ cyclotomic k ℤ ∣ p
  let Eₘ := fun p : ℤ[X] ↦ ∃ k, 3 ≤ k.totient ∧ k.totient < L ∧ cyclotomic k ℤ ∣ p
  let Eₕ := fun p : ℤ[X] ↦ ∃ k, 0 < k ∧ L ≤ k.totient ∧ cyclotomic k ℤ ∣ p
  calc
    _ ≤ binaryProbability (n - 1) (fun p ↦ E₂ p ∨ Eₘ p ∨ Eₕ p) := by
      apply uniformProbability_mono
      rintro w ⟨k, hk, hd⟩
      by_cases htwo : k.totient = 2
      · exact Or.inl ⟨k, htwo, hd⟩
      · by_cases hL : k.totient < L
        · exact Or.inr (Or.inl ⟨k, by omega, hL, hd⟩)
        · exact Or.inr (Or.inr ⟨k, Nat.totient_pos.mp (by omega), by omega, hd⟩)
    _ ≤ binaryProbability (n - 1) E₂ +
        (binaryProbability (n - 1) Eₘ + binaryProbability (n - 1) Eₕ) := by
      exact (binaryProbability_or_le_add (n - 1) E₂ (fun p ↦ Eₘ p ∨ Eₕ p)).trans
        (add_le_add le_rfl (binaryProbability_or_le_add (n - 1) Eₘ Eₕ))
    _ ≤ 1024 / (n : ℝ) +
        (1024 * (L : ℝ) ^ 5 / ((n : ℝ) * Real.sqrt (n : ℝ)) +
          4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ L) :=
      add_le_add (binaryProbability_cyclotomic_degree_two_le hn)
        (add_le_add (binaryProbability_cyclotomic_intermediate_le hn hsmall)
          (binaryProbability_high_cyclotomic_le hn L))
    _ = _ := by ring

end OdlyzkoPoonen
