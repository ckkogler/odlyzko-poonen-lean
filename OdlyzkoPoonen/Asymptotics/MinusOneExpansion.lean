import OdlyzkoPoonen.Asymptotics.MinusOneEvenCorrection
import OdlyzkoPoonen.Asymptotics.MinusOneOddCorrection
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Parity-dependent correction to the minus-one root probability

The relative coefficient is `-17/4` for even degree and `1/4` for odd degree.
The finite remainder keeps the additional square-root decay; in particular
the displayed two-term expansion has an `O(n^(-2))` error.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics

noncomputable def minusOneRelativeCorrection (n : ℕ) : ℝ :=
  if n % 2 = 0 then -17 / 4 else 1 / 4

theorem binaryProbability_minus_one_relative_error {n : ℕ} (hn : 3 ≤ n) :
    |Real.sqrt (Real.pi * (n : ℝ) / 2) *
        binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) -
      (1 + minusOneRelativeCorrection n / (n : ℝ))| ≤ 27 / (n : ℝ) ^ 2 := by
  let r := n / 2
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnr : (n : ℝ) ≤ 3 * (r : ℝ) := by
    exact_mod_cast (show n ≤ 3 * r by dsimp [r]; omega)
  have hscale : 3 / (r : ℝ) ^ 2 ≤ 27 / (n : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hsq : (n : ℝ) ^ 2 ≤ (3 * (r : ℝ)) ^ 2 := by gcongr
    nlinarith
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hn' : n = 2 * r := by dsimp [r]; omega
    have hs : Real.sqrt (Real.pi * (n : ℝ) / 2) = Real.sqrt (Real.pi * (r : ℝ)) := by
      congr 1
      rw [hn']
      push_cast
      ring
    have hc : 1 + minusOneRelativeCorrection n / (n : ℝ) =
        1 - 17 / (8 * (r : ℝ)) := by
      rw [minusOneRelativeCorrection, ite_eq_left he, hn']
      push_cast
      ring
    have h := binaryProbability_minus_one_even_first_correction hr
    rw [hs, hc, hn']
    exact h.trans (by simpa only [hn'] using hscale)
  · have hn' : n = 2 * r + 1 := by dsimp [r]; omega
    have hc : 1 + minusOneRelativeCorrection n / (n : ℝ) =
        1 + 1 / (4 * (2 * (r : ℝ) + 1)) := by
      rw [minusOneRelativeCorrection, ite_eq_right (by omega : ¬ n % 2 = 0), hn']
      push_cast
      field_simp
    have h := binaryProbability_minus_one_odd_first_correction hr
    have h' : |Real.sqrt (Real.pi * (2 * (r : ℝ) + 1) / 2) *
        binaryProbability (2 * r) (fun p ↦ p.eval (-1) = 0) -
        (1 + 1 / (4 * (2 * (r : ℝ) + 1)))| ≤ 3 / (r : ℝ) ^ 2 :=
      h.trans (by gcongr; norm_num)
    rw [hc, hn']
    simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one] using h'.trans (by
        simpa only [hn', Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hscale)

/-- An explicit absolute error for the parity-dependent minus-one expansion. -/
theorem binaryProbability_minus_one_first_correction_error {n : ℕ} (hn : 3 ≤ n) :
    |binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) -
      Real.sqrt (2 / (Real.pi * (n : ℝ))) *
        (1 + minusOneRelativeCorrection n / (n : ℝ))| ≤
      27 / ((n : ℝ) ^ 2 * Real.sqrt (Real.pi * (n : ℝ) / 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let s := Real.sqrt (Real.pi * (n : ℝ) / 2)
  have hs : 0 < s := by dsimp [s]; positivity
  have hi : Real.sqrt (2 / (Real.pi * (n : ℝ))) = 1 / s := by
    calc
      _ = Real.sqrt (1 / (Real.pi * (n : ℝ) / 2)) := by congr 1; ring
      _ = _ := by rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
  have he : binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) -
      (1 / s) * (1 + minusOneRelativeCorrection n / (n : ℝ)) =
      (s * binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) -
        (1 + minusOneRelativeCorrection n / (n : ℝ))) / s := by field_simp
  rw [hi, he, abs_div, abs_of_pos hs]
  calc
    _ ≤ (27 / (n : ℝ) ^ 2) / s := div_le_div_of_nonneg_right
      (binaryProbability_minus_one_relative_error hn) hs.le
    _ = _ := by ring

theorem binaryProbability_minus_one_first_correction_asymptotic :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ p.eval (-1) = 0) -
      Real.sqrt (2 / (Real.pi * (n : ℝ))) *
        (1 + minusOneRelativeCorrection n / (n : ℝ))) =O[atTop]
      (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) := by
  refine isBigO_iff.mpr ⟨27, eventually_atTop.mpr ⟨3, ?_⟩⟩
  intro n hn
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (Real.pi * (n : ℝ) / 2) := by
    apply Real.one_le_sqrt.mpr
    nlinarith [Real.two_le_pi]
  have h := binaryProbability_minus_one_first_correction_error hn
  have h' : 27 / ((n : ℝ) ^ 2 * Real.sqrt (Real.pi * (n : ℝ) / 2)) ≤
      27 * (1 / (n : ℝ) ^ 2) := by
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [sq_nonneg (n : ℝ)]
  have hp : (0 : ℝ) ≤ 1 / (n : ℝ) ^ 2 := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using h.trans h'

end OdlyzkoPoonen
