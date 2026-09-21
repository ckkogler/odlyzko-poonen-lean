import OdlyzkoPoonen.Asymptotics.MonicDeterminantLeadingTerm

/-!
# Exact constants in the three-term reducibility expansion
-/

namespace OdlyzkoPoonen

lemma small_cyclotomic_degree_two_constant :
    6 / Real.pi / Real.sqrt 3 + 8 / Real.pi / Real.sqrt 4 +
      12 / Real.pi / Real.sqrt 12 = 4 * (1 + Real.sqrt 3) / Real.pi := by
  have h12 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
    rw [show (12 : ℝ) = 4 * 3 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  rw [h12]
  norm_num
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

lemma rpow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

lemma small_cyclotomic_degree_three_constant :
    (12 / Real.pi) ^ (3 / 2 : ℝ) / Real.sqrt 72 +
      (8 / Real.pi) ^ (3 / 2 : ℝ) / Real.sqrt 4 +
      (12 / Real.pi) ^ (3 / 2 : ℝ) / Real.sqrt 8 =
      2 * Real.sqrt (2 / Real.pi) * (4 * (1 + Real.sqrt 3) / Real.pi) := by
  have h12 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
    rw [show (12 : ℝ) = 4 * 3 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
  have h72 : Real.sqrt 72 = 6 * Real.sqrt 2 := by
    rw [show (72 : ℝ) = 36 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num
  rw [rpow_three_halves_eq_mul_sqrt (by positivity),
    rpow_three_halves_eq_mul_sqrt (by positivity)]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 12),
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 8),
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), h12, h72, h8]
  norm_num
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp
  ring_nf
  norm_num [Real.sq_sqrt]
  ring

end OdlyzkoPoonen
