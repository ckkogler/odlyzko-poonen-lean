import OdlyzkoPoonen.Asymptotics.MinusOneParity
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The full asymptotic for a root at minus one

For every original degree `n ≥ 3`, the error from `sqrt(2/(pi*n))` is at most
`18*n^(-3/2)`. The passage from the two parity formulas uses `r=n/2` and
explicit comparison of the denominators. The probability always refers to the
original uniform polynomial family, with `n-1` internal bits.
-/

namespace OdlyzkoPoonen
open Filter
open scoped Topology

lemma binaryProbability_minus_one_error_bound {n : ℕ} (hn : 3 ≤ n) :
    |binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) -
      Real.sqrt (2 / (Real.pi * (n : ℝ)))| ≤
        18 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
  let r := n / 2
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnr : n ≤ 3 * r := by dsimp [r]; omega
  have hscale : 3 / ((r : ℝ) * Real.sqrt (r : ℝ)) ≤
      18 / ((n : ℝ) * Real.sqrt (n : ℝ)) :=
    inverse_three_halves_comparison hr0 hn0 (by exact_mod_cast hnr)
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hn' : n = 2 * r := by dsimp [r]; omega
    simpa only [hn', Nat.cast_mul, Nat.cast_ofNat] using
      (binaryProbability_minus_one_even_error hr).trans hscale
  · have hn' : n = 2 * r + 1 := by dsimp [r]; omega
    simpa only [hn', Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using
      (binaryProbability_minus_one_odd_error hr).trans hscale

/-- A uniform quantitative version of the minus-one asymptotic. -/
theorem binaryProbability_minus_one_error_rpow {n : ℕ} (hn : 3 ≤ n) :
    |binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) -
      Real.sqrt (2 / (Real.pi * (n : ℝ)))| ≤ 18 * (n : ℝ) ^ (-3 / 2 : ℝ) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [rpow_neg_three_halves hn0, mul_one_div]
  exact binaryProbability_minus_one_error_bound hn

/-- The source's full `O(n^(-3/2))` remainder, including both degree parities. -/
theorem binaryProbability_minus_one_asymptotic :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) -
      Real.sqrt (2 / (Real.pi * (n : ℝ)))) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-3 / 2 : ℝ)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨18, eventually_atTop.mpr ⟨3, ?_⟩⟩
  intro n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    using binaryProbability_minus_one_error_rpow hn

lemma tendsto_minus_one_leading_term :
    Tendsto (fun n : ℕ ↦ Real.sqrt (2 / (Real.pi * (n : ℝ)))) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ ↦ 2 / (Real.pi * (n : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.const_mul_atTop Real.pi_pos)
  simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hd

lemma tendsto_minus_one_probability :
    Tendsto (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-3 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (y := 3 / 2) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have he := binaryProbability_minus_one_asymptotic.trans_tendsto hp
  simpa only [sub_add_cancel, add_zero] using he.add tendsto_minus_one_leading_term

end OdlyzkoPoonen
