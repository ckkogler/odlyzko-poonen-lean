import OdlyzkoPoonen.Asymptotics.AnchoredDifferences

/-!
# Exponential error with a free upper endpoint

Summing the geometric error more precisely preserves the rate `12^(n/4)`
when the upper endpoint is free. Thus the finite-union decomposition gives
the same exponential rate as in the fixed-endpoint problem.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped BigOperators

theorem anchoredDifferenceMultisetFamily_exponential_error_bound (n : ℕ) :
    |((anchoredDifferenceMultisetFamily n).card : ℝ) - (2 : ℝ) ^ n / 2| ≤
      (1 / 2 + 32 * (12 : ℝ) ^ (1 / 4 : ℝ) /
        ((12 : ℝ) ^ (1 / 4 : ℝ) - 1)) * (12 : ℝ) ^ ((n : ℝ) / 4) := by
  let q : ℝ := (12 : ℝ) ^ (1 / 4 : ℝ)
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hq0 : 0 < q := lt_trans (by norm_num) hq
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
      32 * q * ((q ^ n - 1) / (q - 1)) := by
    calc
      _ ≤ ∑ d ∈ Finset.range n, 32 * q ^ (d + 1) := by
        apply Finset.sum_le_sum
        intro d hd
        simpa only [Nat.add_sub_cancel, twelve_rpow_quarter_eq_pow] using
          differenceMultisetFamily_error_bound (n := d + 1) (by omega)
      _ = 32 * q * (∑ d ∈ Finset.range n, q ^ d) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [pow_succ]
        ring
      _ = _ := by rw [geom_sum_eq (ne_of_gt hq)]
  have habs : |((anchoredDifferenceMultisetFamily n).card : ℝ) - (2 : ℝ) ^ n / 2| ≤
      1 / 2 + 32 * q * ((q ^ n - 1) / (q - 1)) := by
    rw [heq]
    calc
      _ ≤ |(1 / 2 : ℝ)| + |∑ d ∈ Finset.range n,
          (((differenceMultisetFamily (d + 1)).card : ℝ) - (2 : ℝ) ^ d / 2)| := abs_add_le _ _
      _ ≤ 1 / 2 + ∑ d ∈ Finset.range n,
          |((differenceMultisetFamily (d + 1)).card : ℝ) - (2 : ℝ) ^ d / 2| := by
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ _ := add_le_add le_rfl hsum
  have hqn : (1 : ℝ) ≤ q ^ n := one_le_pow₀ hq.le
  have hc : 0 ≤ 32 * q / (q - 1) := by positivity
  have he : 32 * q * ((q ^ n - 1) / (q - 1)) =
      (32 * q / (q - 1)) * q ^ n - 32 * q / (q - 1) := by ring
  rw [he] at habs
  rw [twelve_rpow_quarter_eq_pow]
  change _ ≤ (1 / 2 + 32 * q / (q - 1)) * q ^ n
  nlinarith

/-- Freeing the upper endpoint preserves the exponential error rate. -/
theorem anchoredDifferenceMultisetFamily_exponential_asymptotic :
    (fun n : ℕ ↦ ((anchoredDifferenceMultisetFamily n).card : ℝ) - (2 : ℝ) ^ (n - 1))
      =O[atTop] (fun n : ℕ ↦ (12 : ℝ) ^ ((n : ℝ) / 4)) := by
  refine isBigO_iff.mpr ⟨1 / 2 + 32 * (12 : ℝ) ^ (1 / 4 : ℝ) /
    ((12 : ℝ) ^ (1 / 4 : ℝ) - 1), eventually_atTop.mpr ⟨1, ?_⟩⟩
  intro n hn
  have h := anchoredDifferenceMultisetFamily_exponential_error_bound n
  have he : (2 : ℝ) ^ n / 2 = (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [show n = n - 1 + 1 by omega, pow_succ]
    ring
  rw [he] at h
  have hp : (0 : ℝ) ≤ (12 : ℝ) ^ ((n : ℝ) / 4) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using h

end OdlyzkoPoonen
