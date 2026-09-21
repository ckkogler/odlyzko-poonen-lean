import OdlyzkoPoonen.Asymptotics.SmallCyclotomicApproximation
import OdlyzkoPoonen.Asymptotics.CyclotomicIntersections
import OdlyzkoPoonen.Probability.FourEventExpansion

/-!
# The seven probabilities governing the first three terms

Up to an error of quadratic order, reducibility is the sum of the four
small cyclotomic events, minus the three intersections involving order two.
All higher intersections are absorbed by the other three pair bounds.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics

/-- The finite probability expression that determines terms above `n⁻²`. -/
noncomputable def fourCyclotomicMainTerm (n : ℕ) : ℝ :=
  binaryProbability (n - 1) (fun p ↦ cyclotomic 2 ℤ ∣ p) +
  binaryProbability (n - 1) (fun p ↦ cyclotomic 3 ℤ ∣ p) +
  binaryProbability (n - 1) (fun p ↦ cyclotomic 4 ℤ ∣ p) +
  binaryProbability (n - 1) (fun p ↦ cyclotomic 6 ℤ ∣ p) -
  binaryProbability (n - 1) (fun p ↦ cyclotomic 2 ℤ ∣ p ∧ cyclotomic 3 ℤ ∣ p) -
  binaryProbability (n - 1) (fun p ↦ cyclotomic 2 ℤ ∣ p ∧ cyclotomic 4 ℤ ∣ p) -
  binaryProbability (n - 1) (fun p ↦ cyclotomic 2 ℤ ∣ p ∧ cyclotomic 6 ℤ ∣ p)

theorem binaryProbability_four_union_sub_mainTerm_isBigO :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ cyclotomic 2 ℤ ∣ p ∨
      cyclotomic 3 ℤ ∣ p ∨ cyclotomic 4 ℤ ∣ p ∨ cyclotomic 6 ℤ ∣ p) -
        fourCyclotomicMainTerm n) =O[atTop] (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by
  have h34 := binaryProbability_cyclotomic_pair_isBigO (k := 3) (l := 4) (R := 2)
    (by decide) (by decide) (by decide) (by decide)
  have h36 := binaryProbability_cyclotomic_pair_isBigO (k := 3) (l := 6) (R := 2)
    (by decide) (by decide) (by decide) (by decide)
  have h46 := binaryProbability_cyclotomic_pair_isBigO (k := 4) (l := 6) (R := 2)
    (by decide) (by decide) (by decide) (by decide)
  refine (Asymptotics.IsBigO.of_norm_eventuallyLE ?_).trans ((h34.add h36).add h46)
  apply Filter.Eventually.of_forall
  intro n
  have he := uniformProbability_four_event_remainder
    (fun w : Fin (n - 1) → Bool ↦ cyclotomic 2 ℤ ∣ wordPolynomial w)
    (fun w : Fin (n - 1) → Bool ↦ cyclotomic 3 ℤ ∣ wordPolynomial w)
    (fun w : Fin (n - 1) → Bool ↦ cyclotomic 4 ℤ ∣ wordPolynomial w)
    (fun w : Fin (n - 1) → Bool ↦ cyclotomic 6 ℤ ∣ wordPolynomial w)
  dsimp only at he
  have hs0 : 0 ≤ binaryProbability (n - 1) (fun p ↦ cyclotomic 3 ℤ ∣ p ∧ cyclotomic 4 ℤ ∣ p) +
      binaryProbability (n - 1) (fun p ↦ cyclotomic 3 ℤ ∣ p ∧ cyclotomic 6 ℤ ∣ p) +
      binaryProbability (n - 1) (fun p ↦ cyclotomic 4 ℤ ∣ p ∧ cyclotomic 6 ℤ ∣ p) :=
    add_nonneg (add_nonneg (uniformProbability_nonneg _) (uniformProbability_nonneg _))
      (uniformProbability_nonneg _)
  simp only [Real.norm_eq_abs]
  rw [abs_sub_comm]
  change |fourCyclotomicMainTerm n - _| ≤ _
  unfold fourCyclotomicMainTerm binaryProbability
  rw [abs_of_nonneg he.1]
  exact he.2

/-- No further cyclotomic event is needed above quadratic error. -/
theorem binaryProbability_reducible_four_event_expansion :
    (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat - fourCyclotomicMainTerm n)
      =O[atTop] (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by
  have h := binaryProbability_reducible_four_cyclotomic_approximation.add
    binaryProbability_four_union_sub_mainTerm_isBigO
  simpa only [sub_add_sub_cancel] using h

end OdlyzkoPoonen
