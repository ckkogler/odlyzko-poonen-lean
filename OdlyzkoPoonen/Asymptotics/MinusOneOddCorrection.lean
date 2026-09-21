import OdlyzkoPoonen.Asymptotics.CentralBinomialExpansion
import OdlyzkoPoonen.Asymptotics.MinusOneMass

/-!
# The first correction for odd degree

For degree `2*r+1`, the probability is a central binomial mass. Comparing
normalized squares gives the relative correction `1/(4*(2*r+1))` directly.
-/

namespace OdlyzkoPoonen

theorem binaryProbability_minus_one_odd_first_correction {r : ℕ} (hr : 1 ≤ r) :
    |Real.sqrt (Real.pi * (2 * (r : ℝ) + 1) / 2) *
        binaryProbability (2 * r) (fun p ↦ p.eval (-1) = 0) -
      (1 + 1 / (4 * (2 * (r : ℝ) + 1)))| ≤ 2 / (r : ℝ) ^ 2 := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  let x := Real.sqrt (Real.pi * (2 * (r : ℝ) + 1) / 2) * centralBinomialMass r
  let a := 1 + 1 / (4 * (2 * (r : ℝ) + 1))
  let b := (2 * (r : ℝ) + 1) / (2 * (r : ℝ))
  have hx : 0 ≤ x := mul_nonneg (Real.sqrt_nonneg _) (centralBinomialMass_pos r).le
  have ha : 1 / 2 ≤ a := by
    have h : 0 ≤ 1 / (4 * (2 * (r : ℝ) + 1)) := by positivity
    dsimp [a]
    linarith
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb2 : b ≤ 2 := by
    dsimp [b]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hx2 : x ^ 2 = b * normalizedCentralBinomialSquare r := by
    dsimp [x, b, normalizedCentralBinomialSquare]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have he := normalizedCentralBinomialSquare_first_correction hr
  have hbase : |b * (1 - 1 / (4 * (r : ℝ))) - a ^ 2| ≤ 1 / (2 * (r : ℝ) ^ 2) := by
    dsimp [b, a]
    apply abs_le.mpr
    constructor <;> field_simp <;> nlinarith [sq_nonneg (r : ℝ)]
  have hsq : |x ^ 2 - a ^ 2| ≤ 1 / (r : ℝ) ^ 2 := by
    rw [hx2]
    calc
      _ = |b * (normalizedCentralBinomialSquare r - (1 - 1 / (4 * (r : ℝ)))) +
          (b * (1 - 1 / (4 * (r : ℝ))) - a ^ 2)| := by congr 1; ring
      _ ≤ |b * (normalizedCentralBinomialSquare r - (1 - 1 / (4 * (r : ℝ))))| +
          |b * (1 - 1 / (4 * (r : ℝ))) - a ^ 2| := abs_add_le _ _
      _ ≤ 2 * (1 / (4 * (r : ℝ) ^ 2)) + 1 / (2 * (r : ℝ) ^ 2) := by
        apply add_le_add _ hbase
        rw [abs_mul, abs_of_nonneg hb0]
        exact mul_le_mul hb2 he (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  rw [binaryProbability_minus_one_odd_eq_central]
  change |x - a| ≤ _
  calc
    _ ≤ 2 * |x ^ 2 - a ^ 2| := abs_sub_le_twice_abs_sq_sub_sq hx ha
    _ ≤ 2 * (1 / (r : ℝ) ^ 2) := by gcongr
    _ = _ := by ring

end OdlyzkoPoonen
