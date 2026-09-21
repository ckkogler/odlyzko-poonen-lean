import OdlyzkoPoonen.Asymptotics.SmallCyclotomicLeadingTerms
import OdlyzkoPoonen.Asymptotics.SmallCyclotomicConstants
import OdlyzkoPoonen.Asymptotics.FourCyclotomicExpansion
import OdlyzkoPoonen.Asymptotics.MinusOneExpansion

/-!
# Explicit three-term reducibility expansion

The polynomial degree is `n`, with `n - 1` independent internal binary
coefficients. The parity term is `-17/4` for even degree and `1/4` for odd degree.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics
open scoped BigOperators Classical

/-- Coefficient of the inverse square root of the degree. -/
noncomputable def reducibilityLeadingCoefficient : ℝ := Real.sqrt (2 / Real.pi)

/-- Coefficient of the inverse degree. -/
noncomputable def reducibilitySecondCoefficient : ℝ :=
  ((4 : ℕ) : ℝ) * (1 + Real.sqrt (3 : ℕ)) / Real.pi

lemma nat_rpow_neg_two (n : ℕ) : (n : ℝ) ^ (-2 : ℝ) = ((n : ℝ) ^ 2)⁻¹ := by
  rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two]

lemma nat_rpow_error_weaken {a : ℝ} (ha : a ≤ -2) :
    (fun n : ℕ ↦ (n : ℝ) ^ a) =O[atTop] (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by
  apply Eventually.isBigO
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a), ← nat_rpow_neg_two]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) ha

lemma minus_one_correction_power_identity {n : ℕ} (hn : 0 < n) :
    Real.sqrt (2 / (Real.pi * (n : ℝ))) * (1 + minusOneRelativeCorrection n / (n : ℝ)) =
      reducibilityLeadingCoefficient * (n : ℝ) ^ (-1 / 2 : ℝ) +
      reducibilityLeadingCoefficient * minusOneRelativeCorrection n *
        (n : ℝ) ^ (-3 / 2 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalf : (n : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt (n : ℝ))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hnR.le,
      ← Real.sqrt_eq_rpow]
  have hthree : (n : ℝ) ^ (-3 / 2 : ℝ) =
      (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ)⁻¹ := by
    rw [show (-3 / 2 : ℝ) = -1 / 2 + -1 by ring, Real.rpow_add hnR, hhalf, Real.rpow_neg_one]
  rw [hhalf, hthree, show 2 / (Real.pi * (n : ℝ)) = (2 / Real.pi) / (n : ℝ) by ring,
    Real.sqrt_div (by positivity)]
  unfold reducibilityLeadingCoefficient
  ring

lemma degreeProbability_cyclotomic_two_correction :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ cyclotomic 2 ℤ ∣ p) -
      (reducibilityLeadingCoefficient * (n : ℝ) ^ (-1 / 2 : ℝ) +
        reducibilityLeadingCoefficient * minusOneRelativeCorrection n *
          (n : ℝ) ^ (-3 / 2 : ℝ)))
      =O[atTop] (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by
  refine binaryProbability_minus_one_first_correction_asymptotic.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [cyclotomic_two_dvd_iff_minus_one, minus_one_correction_power_identity hn]
  · exact Eventually.of_forall (fun n ↦ one_div _)

lemma cyclotomic_pair_product_dvd_iff {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hkl : k ≠ l) (p : ℤ[X]) :
    cyclotomic k ℤ * cyclotomic l ℤ ∣ p ↔
      cyclotomic k ℤ ∣ p ∧ cyclotomic l ℤ ∣ p := by
  have hs : ∀ j ∈ ({k, l} : Finset ℕ), 0 < j := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact hk
    · exact hl
  simpa [cyclotomicProduct, hkl] using cyclotomicProduct_dvd_iff hs p

/-- The seven small-event probabilities give the explicit three-term expression. -/
lemma fourCyclotomicMainTerm_explicit_expansion :
    (fun n : ℕ ↦ fourCyclotomicMainTerm n -
      (reducibilityLeadingCoefficient * (n : ℝ) ^ (-1 / 2 : ℝ) +
        reducibilitySecondCoefficient * (n : ℝ) ^ (-1 : ℝ) +
        reducibilityLeadingCoefficient *
          (minusOneRelativeCorrection n - 2 * reducibilitySecondCoefficient) *
          (n : ℝ) ^ (-3 / 2 : ℝ)))
      =O[atTop] (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by
  have h2 := degreeProbability_cyclotomic_two_correction
  have h3 := degreeProbability_cyclotomic_three_leading_term.trans
    (nat_rpow_error_weaken (by norm_num : (-2 : ℝ) ≤ -2))
  have h4 := degreeProbability_cyclotomic_four_leading_term.trans
    (nat_rpow_error_weaken (by norm_num : (-2 : ℝ) ≤ -2))
  have h6 := degreeProbability_cyclotomic_six_leading_term.trans
    (nat_rpow_error_weaken (by norm_num : (-2 : ℝ) ≤ -2))
  have h23 := degreeProbability_cyclotomic_two_three_leading_term.trans
    (nat_rpow_error_weaken (by norm_num : (-5 / 2 : ℝ) ≤ -2))
  have h24 := degreeProbability_cyclotomic_two_four_leading_term.trans
    (nat_rpow_error_weaken (by norm_num : (-5 / 2 : ℝ) ≤ -2))
  have h26 := degreeProbability_cyclotomic_two_six_leading_term.trans
    (nat_rpow_error_weaken (by norm_num : (-5 / 2 : ℝ) ≤ -2))
  simp only [cyclotomic_pair_product_dvd_iff (by decide : 0 < 2)
    (by decide : 0 < 3) (by decide : 2 ≠ 3)] at h23
  simp only [cyclotomic_pair_product_dvd_iff (by decide : 0 < 2)
    (by decide : 0 < 4) (by decide : 2 ≠ 4)] at h24
  simp only [cyclotomic_pair_product_dvd_iff (by decide : 0 < 2)
    (by decide : 0 < 6) (by decide : 2 ≠ 6)] at h26
  have h := (((((h2.add h3).add h4).add h6).sub h23).sub h24).sub h26
  convert! h using 1
  funext n
  dsimp [fourCyclotomicMainTerm, reducibilityLeadingCoefficient, reducibilitySecondCoefficient]
  linear_combination (n : ℝ) ^ (-1 : ℝ) * small_cyclotomic_degree_two_constant -
    (n : ℝ) ^ (-3 / 2 : ℝ) * small_cyclotomic_degree_three_constant

/-- The explicit expansion through inverse degree to the power three halves,
with a uniform quadratic error and the degree-dependent parity correction. -/
theorem binaryProbability_reducible_three_term_expansion :
    (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      (reducibilityLeadingCoefficient * (n : ℝ) ^ (-1 / 2 : ℝ) +
        reducibilitySecondCoefficient * (n : ℝ) ^ (-1 : ℝ) +
        reducibilityLeadingCoefficient *
          (minusOneRelativeCorrection n - 2 * reducibilitySecondCoefficient) *
          (n : ℝ) ^ (-3 / 2 : ℝ)))
      =O[atTop] (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by
  have h := binaryProbability_reducible_four_event_expansion.add
    fourCyclotomicMainTerm_explicit_expansion
  simpa only [sub_add_sub_cancel] using h

end OdlyzkoPoonen
