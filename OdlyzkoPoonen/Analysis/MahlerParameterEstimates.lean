import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# Explicit parameter estimates for the Mahler bound

At logarithmic degree scale `L`, the integer choices are the ceilings of `L`
and `L² log L`. Rounding and elementary logarithmic estimates suffice for the
coarse determinant budget; every constant is independent of the polynomial.
-/

namespace OdlyzkoPoonen

lemma mahler_parameter_ceil_bounds {L : ℝ} (hL : 1 ≤ L)
    (hlog : 3040 ≤ Real.log L) :
    L ≤ (⌈L⌉₊ : ℝ) ∧ (⌈L⌉₊ : ℝ) ≤ 2 * L ∧
      L ^ 2 * Real.log L ≤ (⌈L ^ 2 * Real.log L⌉₊ : ℝ) ∧
      (⌈L ^ 2 * Real.log L⌉₊ : ℝ) ≤ 2 * L ^ 2 * Real.log L ∧
      L ≤ (⌈L ^ 2 * Real.log L⌉₊ : ℝ) ∧
      1 < (⌈L ^ 2 * Real.log L⌉₊ : ℝ) := by
  have hL0 : 0 ≤ L := by linarith
  have hlog1 : 1 ≤ Real.log L := by linarith
  have hsq : L ≤ L ^ 2 := by nlinarith
  have hscale : L ≤ L ^ 2 * Real.log L :=
    hsq.trans (le_mul_of_one_le_right (sq_nonneg L) hlog1)
  have hn := Nat.le_ceil (L ^ 2 * Real.log L)
  have hkupper := Nat.ceil_lt_add_one hL0
  have hnupper := Nat.ceil_lt_add_one (hL0.trans hscale)
  have hlarge : 2 ≤ L ^ 2 * Real.log L := by
    have := mul_le_mul_of_nonneg_left hlog (sq_nonneg L)
    nlinarith
  exact ⟨Nat.le_ceil L, by linarith, hn, by linarith,
    hscale.trans hn, by linarith⟩

lemma mahler_prime_scale_log_lower {L n : ℝ} (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log L) (hn : L ^ 2 * Real.log L ≤ n) :
    2 * Real.log L ≤ Real.log n := by
  have hL0 : 0 < L := by linarith
  have hsq : L ^ 2 ≤ n := (le_mul_of_one_le_right (sq_nonneg L) hlog).trans hn
  simpa only [Real.log_pow, Nat.cast_ofNat] using
    Real.log_le_log (sq_pos_of_pos hL0) hsq

lemma mahler_prime_card_budget {L n s : ℝ} (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log L) (hn : L ^ 2 * Real.log L ≤ n)
    (hnup : n ≤ 2 * L ^ 2 * Real.log L)
    (hs : s ≤ 16 * n / Real.log n) : s ≤ 16 * L ^ 2 := by
  have hlogn := mahler_prime_scale_log_lower hL hlog hn
  have hpos : 0 < Real.log n := by linarith
  apply hs.trans
  apply (div_le_iff₀ hpos).mpr
  have h := mul_le_mul_of_nonneg_left hlogn (show 0 ≤ 16 * L ^ 2 by positivity)
  nlinarith

lemma mahler_prime_sum_budget {L n s S : ℝ} (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log L) (hnup : n ≤ 2 * L ^ 2 * Real.log L)
    (hs : 0 ≤ s) (hsup : s ≤ 16 * L ^ 2) (hS : S ≤ s * (8 * n)) :
    S ≤ 256 * L ^ 4 * Real.log L := by
  calc
    S ≤ s * (8 * n) := hS
    _ ≤ s * (8 * (2 * L ^ 2 * Real.log L)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnup (by norm_num)) hs
    _ ≤ (16 * L ^ 2) * (8 * (2 * L ^ 2 * Real.log L)) :=
      mul_le_mul_of_nonneg_right hsup (by positivity)
    _ = _ := by ring

lemma mahler_bad_prime_log_budget {d L n : ℝ} (hd : 0 < d)
    (hLd : Real.log d = L) (hL : 1 ≤ L) (hlog : 3040 ≤ Real.log L)
    (hn : L ^ 2 * Real.log L ≤ n) : Real.log (2 * d ^ 4) ≤ n / 2 := by
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hd.ne'), Real.log_pow, hLd]
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hsq : L ≤ L ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hlog (sq_nonneg L)
  norm_num at htwo ⊢
  nlinarith

lemma mahler_node_log_budget {d L k s : ℝ} (hd : 1 ≤ d)
    (hLd : Real.log d = L) (hL : 1 ≤ L) (hk : L ≤ k) (hkup : k ≤ 2 * L)
    (hs : 0 ≤ s) (hsup : s ≤ 16 * L ^ 2) :
    0 ≤ Real.log (d * (k + s)) ∧ Real.log (d * (k + s)) ≤ 20 * L := by
  have hd0 : 0 < d := by linarith
  have hL0 : 0 < L := by linarith
  have hks : 1 ≤ k + s := by linarith
  have hks0 : 0 < k + s := by linarith
  have hsq : L ≤ L ^ 2 := by nlinarith
  have hksup : k + s ≤ 18 * L ^ 2 := by linarith
  refine ⟨Real.log_nonneg (by nlinarith), ?_⟩
  rw [Real.log_mul hd0.ne' hks0.ne', hLd]
  have hb := Real.log_le_log hks0 hksup
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hL0.ne'), Real.log_pow] at hb
  have h18 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 18)
  have hl := Real.log_le_sub_one_of_pos hL0
  norm_num at hb h18
  linarith

end OdlyzkoPoonen
