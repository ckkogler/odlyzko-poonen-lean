import OdlyzkoPoonen.Probability.CyclotomicRangeSum
import OdlyzkoPoonen.Asymptotics.CyclotomicCutoff

/-!
# The full higher-cyclotomic probability estimate

For the original degree-`n` endpoint-one binary polynomial, the probability of
any cyclotomic divisor of degree at least two is `O(1/n)`. A proved logarithmic
cutoff includes every possible order and gives the absolute bound `2052/n`
for all sufficiently large degrees. No concentration, independence, order
estimate or asymptotic is assumed in the final theorem.
-/

namespace OdlyzkoPoonen
open Filter
open scoped Topology

lemma cyclotomic_cutoff_tail_le {n : ℕ} (hn : 1 ≤ n) :
    4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ cyclotomicDegreeCutoff n ≤ 4 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (n : ℝ) ≤ (n : ℝ) ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hn1 (by norm_num : 1 ≤ 6)
  calc
    _ ≤ 4 * (n : ℝ) ^ 2 / (n : ℝ) ^ 8 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_eight_le_two_pow_cyclotomicDegreeCutoff n)
    _ = 4 / (n : ℝ) ^ 6 := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hnR hp

lemma eventually_binaryProbability_higher_cyclotomic_le :
    ∀ᶠ n : ℕ in atTop,
      binaryProbability (n - 1) HasHigherCyclotomicDivisor ≤ 2052 / (n : ℝ) := by
  have hcut := (tendsto_cyclotomicDegreeCutoff_pow_div_sqrt 5).eventually_le_const
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop 1, eventually_cyclotomic_cutoff_scale_le_one, hcut]
    with n hn hs hL
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmid : 1024 * (cyclotomicDegreeCutoff n : ℝ) ^ 5 /
      ((n : ℝ) * Real.sqrt (n : ℝ)) ≤ 1024 / (n : ℝ) := by
    calc
      _ = (1024 / (n : ℝ)) *
          ((cyclotomicDegreeCutoff n : ℝ) ^ 5 / Real.sqrt (n : ℝ)) := by ring
      _ ≤ (1024 / (n : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      _ = _ := mul_one _
  calc
    _ ≤ 1024 / (n : ℝ) + 1024 * (cyclotomicDegreeCutoff n : ℝ) ^ 5 /
        ((n : ℝ) * Real.sqrt (n : ℝ)) +
          4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ cyclotomicDegreeCutoff n :=
      binaryProbability_higher_cyclotomic_range_sum hn hs
    _ ≤ 1024 / (n : ℝ) + 1024 / (n : ℝ) + 4 / (n : ℝ) :=
      add_le_add (add_le_add le_rfl hmid) (cyclotomic_cutoff_tail_le hn)
    _ = _ := by ring

/-- An absolute effective coefficient, with a rigorously derived sufficiently-large threshold. -/
theorem exists_threshold_higher_cyclotomic_bound :
    ∃ N : ℕ, ∀ n ≥ N,
      0 ≤ binaryProbability (n - 1) HasHigherCyclotomicDivisor ∧
        binaryProbability (n - 1) HasHigherCyclotomicDivisor ≤ 2052 / (n : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_binaryProbability_higher_cyclotomic_le
  exact ⟨N, fun n hn ↦ ⟨uniformProbability_nonneg _, hN n hn⟩⟩

/-- The source's complete higher-cyclotomic bound (3.4), under its original probability law. -/
theorem binaryProbability_higher_cyclotomic_isBigO :
    (fun n : ℕ ↦ binaryProbability (n - 1) HasHigherCyclotomicDivisor) =O[atTop]
      (fun n : ℕ ↦ 1 / (n : ℝ)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨2052, ?_⟩
  filter_upwards [eventually_binaryProbability_higher_cyclotomic_le] with n hn
  have hp0 : 0 ≤ binaryProbability (n - 1) HasHigherCyclotomicDivisor :=
    uniformProbability_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp0,
    abs_of_nonneg (show 0 ≤ 1 / (n : ℝ) by positivity), mul_one_div] using hn

lemma tendsto_higher_cyclotomic_probability :
    Tendsto (fun n : ℕ ↦ binaryProbability (n - 1) HasHigherCyclotomicDivisor)
      atTop (𝓝 0) :=
  binaryProbability_higher_cyclotomic_isBigO.trans_tendsto
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)

end OdlyzkoPoonen
