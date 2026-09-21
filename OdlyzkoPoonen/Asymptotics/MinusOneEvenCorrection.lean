import OdlyzkoPoonen.Asymptotics.CentralBinomialExpansion
import OdlyzkoPoonen.Asymptotics.MinusOneMass

/-!
# The first correction for even degree

The exact factor `(r-1)/(r+1)` combines with the central-binomial correction.
At degree `2*r`, the resulting relative correction is `-17/(8*r)`.
-/

namespace OdlyzkoPoonen

theorem binaryProbability_minus_one_even_first_correction {r : ℕ} (hr : 1 ≤ r) :
    |Real.sqrt (Real.pi * (r : ℝ)) *
        binaryProbability (2 * r - 1) (fun p ↦ p.eval (-1) = 0) -
      (1 - 17 / (8 * (r : ℝ)))| ≤ 3 / (r : ℝ) ^ 2 := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  let a := ((r : ℝ) - 1) / ((r : ℝ) + 1)
  let t := Real.sqrt (Real.pi * (r : ℝ)) * centralBinomialMass r
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_one (by positivity)).mpr
    linarith
  have ht : |t - (1 - 1 / (8 * (r : ℝ)))| ≤ 1 / (2 * (r : ℝ) ^ 2) :=
    normalizedCentralBinomialMass_first_correction hr
  have he : a * t - (1 - 17 / (8 * (r : ℝ))) =
      a * (t - (1 - 1 / (8 * (r : ℝ)))) + 9 / (4 * (r : ℝ) * ((r : ℝ) + 1)) := by
    dsimp [a]
    field_simp
    ring
  have hrem : 9 / (4 * (r : ℝ) * ((r : ℝ) + 1)) ≤ 9 / (4 * (r : ℝ) ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have hprod : |a * (t - (1 - 1 / (8 * (r : ℝ))))| ≤ 1 / (2 * (r : ℝ) ^ 2) := by
    rw [abs_mul, abs_of_nonneg ha0]
    exact (mul_le_mul_of_nonneg_left ht ha0).trans (by
      simpa using mul_le_mul_of_nonneg_right ha1
        (show 0 ≤ 1 / (2 * (r : ℝ) ^ 2) by positivity))
  rw [binaryProbability_minus_one_even_eq_central hr]
  change |Real.sqrt (Real.pi * (r : ℝ)) * (a * centralBinomialMass r) -
    (1 - 17 / (8 * (r : ℝ)))| ≤ _
  rw [show Real.sqrt (Real.pi * (r : ℝ)) * (a * centralBinomialMass r) = a * t by
    dsimp [t]; ring, he]
  calc
    _ ≤ |a * (t - (1 - 1 / (8 * (r : ℝ))))| +
        |9 / (4 * (r : ℝ) * ((r : ℝ) + 1))| := abs_add_le _ _
    _ ≤ 1 / (2 * (r : ℝ) ^ 2) + 9 / (4 * (r : ℝ) ^ 2) := by
      rw [abs_of_nonneg (by positivity : 0 ≤ 9 / (4 * (r : ℝ) * ((r : ℝ) + 1)))]
      exact add_le_add hprod hrem
    _ ≤ _ := by field_simp; nlinarith

end OdlyzkoPoonen
