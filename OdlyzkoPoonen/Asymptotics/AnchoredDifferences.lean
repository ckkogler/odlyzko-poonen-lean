import OdlyzkoPoonen.Asymptotics.DifferenceMultisets
import OdlyzkoPoonen.Combinatorics.AnchoredDifferences
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Asymptotic count with a free upper endpoint

The number of distinct signed difference multisets of subsets of `{0, ..., n}`
containing zero is `2^(n-1) + o(2^n)`. Summing the fixed-endpoint error gives
a bound by `33 * n * 12^(n/4)`, which is exponentially smaller than `2^n`.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped BigOperators

lemma twelve_rpow_quarter_eq_pow (n : ℕ) :
    (12 : ℝ) ^ ((n : ℝ) / 4) = ((12 : ℝ) ^ (1 / 4 : ℝ)) ^ n := by
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 12)]
  congr 1
  ring

lemma twelve_rpow_quarter_lt_two : (12 : ℝ) ^ (1 / 4 : ℝ) < 2 := by
  have h : ((12 : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = 12 := by
    simpa using Real.rpow_inv_natCast_pow (x := (12 : ℝ)) (n := 4)
      (by norm_num) (by norm_num)
  apply (pow_lt_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _)
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [h]
  norm_num

/-- An explicit summatory bound, valid at every positive degree. -/
theorem anchoredDifferenceMultisetFamily_error_bound {n : ℕ} (hn : 1 ≤ n) :
    |((anchoredDifferenceMultisetFamily n).card : ℝ) - (2 : ℝ) ^ n / 2| ≤
      33 * (n : ℝ) * (12 : ℝ) ^ ((n : ℝ) / 4) := by
  let q : ℝ := (12 : ℝ) ^ (1 / 4 : ℝ)
  have hq : 1 ≤ q := Real.one_le_rpow (by norm_num) (by norm_num)
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have htotal : ((anchoredDifferenceMultisetFamily n).card : ℝ) =
      1 + ∑ d ∈ Finset.range n, ((differenceMultisetFamily (d + 1)).card : ℝ) := by
    exact_mod_cast card_anchoredDifferenceMultisetFamily_succ_sum n
  have hgeom : (∑ d ∈ Finset.range n, (2 : ℝ) ^ d / 2) =
      ((2 : ℝ) ^ n - 1) / 2 := by
    rw [← Finset.sum_div]
    congr 1
    have h := geom_sum_mul (2 : ℝ) n
    norm_num at h
    exact h
  have heq : ((anchoredDifferenceMultisetFamily n).card : ℝ) - (2 : ℝ) ^ n / 2 =
      1 / 2 + ∑ d ∈ Finset.range n,
        (((differenceMultisetFamily (d + 1)).card : ℝ) - (2 : ℝ) ^ d / 2) := by
    rw [Finset.sum_sub_distrib, hgeom, htotal]
    ring
  have hsum : (∑ d ∈ Finset.range n,
      |((differenceMultisetFamily (d + 1)).card : ℝ) - (2 : ℝ) ^ d / 2|) ≤
      (n : ℝ) * (32 * q ^ n) := by
    calc
      _ ≤ ∑ d ∈ Finset.range n, 32 * q ^ n := by
        apply Finset.sum_le_sum
        intro d hd
        have h := differenceMultisetFamily_error_bound (n := d + 1) (by omega)
        simp only [Nat.add_sub_cancel, twelve_rpow_quarter_eq_pow] at h
        apply h.trans
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact pow_le_pow_right₀ hq (by have := Finset.mem_range.mp hd; omega)
      _ = _ := by simp
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hqn : (1 : ℝ) ≤ q ^ n := one_le_pow₀ hq
  have hnq : (1 : ℝ) ≤ (n : ℝ) * q ^ n := by nlinarith
  rw [heq, twelve_rpow_quarter_eq_pow]
  change |1 / 2 + ∑ d ∈ Finset.range n,
      (((differenceMultisetFamily (d + 1)).card : ℝ) - (2 : ℝ) ^ d / 2)| ≤
    33 * (n : ℝ) * q ^ n
  calc
    _ ≤ |(1 / 2 : ℝ)| + |∑ d ∈ Finset.range n,
        (((differenceMultisetFamily (d + 1)).card : ℝ) - (2 : ℝ) ^ d / 2)| := abs_add_le _ _
    _ ≤ 1 / 2 + ∑ d ∈ Finset.range n,
        |((differenceMultisetFamily (d + 1)).card : ℝ) - (2 : ℝ) ^ d / 2| := by
      norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := by nlinarith

/-- The free-endpoint signed-difference count has relative error tending to zero. -/
theorem anchoredDifferenceMultisetFamily_asymptotic :
    (fun n : ℕ ↦ ((anchoredDifferenceMultisetFamily n).card : ℝ) - (2 : ℝ) ^ (n - 1))
      =o[atTop] (fun n : ℕ ↦ (2 : ℝ) ^ n) := by
  let q : ℝ := (12 : ℝ) ^ (1 / 4 : ℝ)
  have hq : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hb : (fun n : ℕ ↦ ((anchoredDifferenceMultisetFamily n).card : ℝ) -
      (2 : ℝ) ^ (n - 1)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) * q ^ n) := by
    refine isBigO_iff.mpr ⟨33, eventually_atTop.mpr ⟨1, ?_⟩⟩
    intro n hn
    have h := anchoredDifferenceMultisetFamily_error_bound hn
    have he : (2 : ℝ) ^ n / 2 = (2 : ℝ) ^ (n - 1) := by
      conv_lhs => rw [show n = n - 1 + 1 by omega, pow_succ]
      ring
    rw [he, twelve_rpow_quarter_eq_pow] at h
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hq n)), mul_assoc] using h
  apply hb.trans_isLittleO
  have hlt : ‖q‖ < (2 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq]
    exact twelve_rpow_quarter_lt_two
  simpa only [pow_one] using
    isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt 1 hlt

end OdlyzkoPoonen
