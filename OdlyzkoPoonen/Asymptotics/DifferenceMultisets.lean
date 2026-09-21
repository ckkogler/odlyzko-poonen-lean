import OdlyzkoPoonen.Combinatorics.DifferenceMultisetCount
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponential error in the number of difference multisets

The finite companion bound and reflection correction give an explicit error
of at most `32 * 12^(n/4)`. The exponent in this bound is real division.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics

lemma difference_multiset_exception_scale_le (n : ℕ) :
    (2 : ℝ) ^ (n - 1) / 2 * (8 * (3 / 4 : ℝ) ^ ((n - 1) / 4)) ≤
      32 * (12 : ℝ) ^ ((n - 1) / 4) := by
  let k := (n - 1) / 4
  let r := (n - 1) % 4
  have hr : r ≤ 3 := by dsimp [r]; omega
  have hsplit : n - 1 = 4 * k + r := by
    dsimp [k, r]
    omega
  have hpow : (2 : ℝ) ^ (n - 1) * (3 / 4 : ℝ) ^ k =
      (2 : ℝ) ^ r * (12 : ℝ) ^ k := by
    rw [hsplit, pow_add, pow_mul]
    calc
      _ = (2 : ℝ) ^ r * ((2 ^ 4 : ℝ) ^ k * (3 / 4 : ℝ) ^ k) := by ring
      _ = (2 : ℝ) ^ r * ((2 ^ 4 : ℝ) * (3 / 4 : ℝ)) ^ k := by rw [mul_pow]
      _ = _ := by norm_num
  have hrpow : (2 : ℝ) ^ r ≤ 8 := by
    have h : (2 : ℝ) ^ r ≤ (2 : ℝ) ^ 3 :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
    norm_num at h
    exact h
  change (2 : ℝ) ^ (n - 1) / 2 * (8 * (3 / 4 : ℝ) ^ k) ≤ 32 * (12 : ℝ) ^ k
  calc
    _ = 4 * ((2 : ℝ) ^ (n - 1) * (3 / 4 : ℝ) ^ k) := by ring
    _ = 4 * ((2 : ℝ) ^ r * (12 : ℝ) ^ k) := by rw [hpow]
    _ ≤ 4 * (8 * (12 : ℝ) ^ k) := by gcongr
    _ = _ := by ring

lemma difference_multiset_reflection_scale_le (n : ℕ) :
    (2 : ℝ) ^ (n / 2) / 2 ≤ 2 * (12 : ℝ) ^ ((n - 1) / 4) := by
  let k := (n - 1) / 4
  have hn : n / 2 ≤ 2 * k + 2 := by dsimp [k]; omega
  have hpow : (2 : ℝ) ^ (n / 2) ≤ 4 * (12 : ℝ) ^ k := by
    calc
      _ ≤ (2 : ℝ) ^ (2 * k + 2) := pow_le_pow_right₀ (by norm_num) hn
      _ = 4 * (4 : ℝ) ^ k := by rw [pow_add, pow_mul]; norm_num; ring
      _ ≤ _ := by gcongr; norm_num
  change (2 : ℝ) ^ (n / 2) / 2 ≤ 2 * (12 : ℝ) ^ k
  linarith

lemma twelve_pow_block_le_rpow (n : ℕ) :
    (12 : ℝ) ^ ((n - 1) / 4) ≤ (12 : ℝ) ^ ((n : ℝ) / 4) := by
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  exact_mod_cast (show (n - 1) / 4 * 4 ≤ n by omega)

/-- A fully explicit finite error bound for the distinct signed differences. -/
theorem differenceMultisetFamily_error_bound {n : ℕ} (hn : 1 ≤ n) :
    |((differenceMultisetFamily n).card : ℝ) - (2 : ℝ) ^ (n - 1) / 2| ≤
      32 * (12 : ℝ) ^ ((n : ℝ) / 4) := by
  obtain ⟨hl, hu⟩ := differenceMultisetFamily_card_bounds hn
  have he := difference_multiset_exception_scale_le n
  have hr := difference_multiset_reflection_scale_le n
  have hp : (0 : ℝ) ≤ 12 ^ ((n - 1) / 4) := by positivity
  have hb : |((differenceMultisetFamily n).card : ℝ) - (2 : ℝ) ^ (n - 1) / 2| ≤
      32 * (12 : ℝ) ^ ((n - 1) / 4) := by
    apply abs_le.mpr
    constructor <;> nlinarith
  exact hb.trans (mul_le_mul_of_nonneg_left (twelve_pow_block_le_rpow n) (by norm_num))

/-- The number of distinct difference multisets is `2^(n-2) + O(12^(n/4))`. -/
theorem differenceMultisetFamily_asymptotic :
    (fun n : ℕ ↦ ((differenceMultisetFamily n).card : ℝ) - (2 : ℝ) ^ (n - 2))
      =O[atTop] (fun n : ℕ ↦ (12 : ℝ) ^ ((n : ℝ) / 4)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨32, eventually_atTop.mpr ⟨2, ?_⟩⟩
  intro n hn
  have h := differenceMultisetFamily_error_bound (show 1 ≤ n by omega)
  have he : (2 : ℝ) ^ (n - 1) / 2 = (2 : ℝ) ^ (n - 2) := by
    rw [show n - 1 = n - 2 + 1 by omega, pow_succ]
    ring
  rw [he] at h
  have hp : (0 : ℝ) ≤ (12 : ℝ) ^ ((n : ℝ) / 4) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using h

end OdlyzkoPoonen
