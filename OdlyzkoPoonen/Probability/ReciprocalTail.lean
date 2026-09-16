import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The reciprocal-divisor geometric tail

The summand from reciprocal counting is `2 * (1/2)^ceil(h/2)`. Its exact tail is
`2 * (1/2)^floor(h/2) + 4 * (1/2)^ceil(h/2)`: subtracting the next tail gives the
summand. Finite telescoping avoids an infinite-series interchange. The final
comparison keeps the real exponent `-L/2`, with constant six for both parities.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

/-- A closed form for the positive geometric tail beginning at degree `L`. -/
noncomputable def reciprocalGeometricTail (L : ℕ) : ℝ :=
  2 * (1 / 2 : ℝ) ^ (L / 2) + 4 * (1 / 2 : ℝ) ^ ((L + 1) / 2)

lemma reciprocal_counting_summand (h : ℕ) :
    (2 : ℝ) ^ (h / 2) * (2 / (2 : ℝ) ^ h) =
      2 * (1 / 2 : ℝ) ^ ((h + 1) / 2) := by
  have hp : (2 : ℝ) ^ h = 2 ^ (h / 2) * 2 ^ ((h + 1) / 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp, one_div_pow]
  field_simp

lemma reciprocalGeometricTail_nonneg (L : ℕ) : 0 ≤ reciprocalGeometricTail L := by
  unfold reciprocalGeometricTail
  positivity

lemma reciprocalGeometricTail_succ (L : ℕ) :
    reciprocalGeometricTail L =
      2 * (1 / 2 : ℝ) ^ ((L + 1) / 2) + reciprocalGeometricTail (L + 1) := by
  unfold reciprocalGeometricTail
  rw [show (L + 1 + 1) / 2 = L / 2 + 1 by omega, pow_succ]
  ring

lemma sum_reciprocal_tail_range (L k : ℕ) :
    (∑ i ∈ Finset.range k, 2 * (1 / 2 : ℝ) ^ ((L + i + 1) / 2)) +
      reciprocalGeometricTail (L + k) = reciprocalGeometricTail L := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have ht := reciprocalGeometricTail_succ (L + k)
    rw [show L + (k + 1) = L + k + 1 by omega]
    linarith

lemma sum_reciprocal_counting_le_tail (L n : ℕ) :
    (∑ h ∈ Finset.Icc L n, (2 : ℝ) ^ (h / 2) * (2 / (2 : ℝ) ^ h)) ≤
      reciprocalGeometricTail L := by
  simp_rw [reciprocal_counting_summand]
  have hs : Finset.Icc L n = Finset.Ico L (n + 1) := by ext h; simp
  rw [hs, Finset.sum_Ico_eq_sum_range]
  have heq := sum_reciprocal_tail_range L (n + 1 - L)
  have hnonneg := reciprocalGeometricTail_nonneg (L + (n + 1 - L))
  linarith

lemma two_rpow_neg_half_even (r : ℕ) :
    (2 : ℝ) ^ (-((2 * r : ℕ) : ℝ) / 2) = (1 / 2 : ℝ) ^ r := by
  have he : -((2 * r : ℕ) : ℝ) / 2 = -(r : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div_pow, one_div]

lemma two_rpow_neg_half_odd (r : ℕ) :
    (2 : ℝ) ^ (-((2 * r + 1 : ℕ) : ℝ) / 2) =
      (1 / 2 : ℝ) ^ r / Real.sqrt 2 := by
  have he : -((2 * r + 1 : ℕ) : ℝ) / 2 = -(r : ℝ) + -(1 / 2 : ℝ) := by
    push_cast
    ring
  rw [he, Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num),
    Real.rpow_natCast, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow,
    one_div_pow, one_div, div_eq_mul_inv]

lemma reciprocalGeometricTail_even (r : ℕ) :
    reciprocalGeometricTail (2 * r) = 6 * (1 / 2 : ℝ) ^ r := by
  unfold reciprocalGeometricTail
  rw [show (2 * r) / 2 = r by omega, show (2 * r + 1) / 2 = r by omega]
  ring

lemma reciprocalGeometricTail_odd (r : ℕ) :
    reciprocalGeometricTail (2 * r + 1) = 4 * (1 / 2 : ℝ) ^ r := by
  unfold reciprocalGeometricTail
  rw [show (2 * r + 1) / 2 = r by omega,
    show (2 * r + 1 + 1) / 2 = r + 1 by omega, pow_succ]
  ring

lemma reciprocalGeometricTail_le_rpow (L : ℕ) :
    reciprocalGeometricTail L ≤ 6 * (2 : ℝ) ^ (-(L : ℝ) / 2) := by
  have hpar : L = 2 * (L / 2) ∨ L = 2 * (L / 2) + 1 := by omega
  rcases hpar with he | ho
  · conv_lhs => rw [he]
    conv_rhs => rw [he]
    rw [reciprocalGeometricTail_even, two_rpow_neg_half_even]
  · conv_lhs => rw [ho]
    conv_rhs => rw [ho]
    rw [reciprocalGeometricTail_odd, two_rpow_neg_half_odd]
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsle : Real.sqrt 2 ≤ 3 / 2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    have hc : (4 : ℝ) ≤ 6 / Real.sqrt 2 := by
      apply (le_div_iff₀ hs).2
      linarith
    calc
      _ ≤ (6 / Real.sqrt 2) * (1 / 2 : ℝ) ^ (L / 2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring

lemma sum_reciprocal_counting_le_rpow (L n : ℕ) :
    (∑ h ∈ Finset.Icc L n, (2 : ℝ) ^ (h / 2) * (2 / (2 : ℝ) ^ h)) ≤
      6 * (2 : ℝ) ^ (-(L : ℝ) / 2) :=
  (sum_reciprocal_counting_le_tail L n).trans (reciprocalGeometricTail_le_rpow L)

end OdlyzkoPoonen
