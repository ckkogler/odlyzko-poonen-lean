import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# A coarse numerical budget for the Mahler argument

Large logarithmic scale makes the prime-weight contribution dominate the
polynomial determinant cost. The constants here are deliberately coarse;
all are absolute, and the resulting lower bound has exponent three.
-/

namespace OdlyzkoPoonen

lemma mahler_log_lower_of_parameter_budget {L k n s S B m : ℝ}
    (hL : 1 ≤ L) (hlog : 3040 ≤ Real.log L)
    (hk : L ≤ k) (hkup : k ≤ 2 * L)
    (hn : L ^ 2 * Real.log L ≤ n)
    (hs : 0 ≤ s) (hsup : s ≤ 16 * L ^ 2)
    (hS : S ≤ 256 * L ^ 4 * Real.log L)
    (hB : 0 ≤ B) (hBup : B ≤ 20 * L) (hm : 0 ≤ m)
    (hmain : k * n / 2 ≤ (k ^ 2 + k + 2 * s) * B + (k + s) * (k + S) * m) :
    1 / (18576 * L ^ 3) ≤ m := by
  have hL0 : 0 < L := by linarith
  have hl1 : 1 ≤ Real.log L := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hA : k ^ 2 + k + 2 * s ≤ 38 * L ^ 2 := by
    have hk2 : k ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ hk0 hkup 2
    nlinarith
  have hks : k + s ≤ 18 * L ^ 2 := by linarith
  have hL4 : L ≤ L ^ 4 * Real.log L := by
    calc
      L = L ^ 1 := by simp
      _ ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hl1
  have hkS : k + S ≤ 258 * L ^ 4 * Real.log L := by linarith
  have hcost : (k ^ 2 + k + 2 * s) * B ≤ 760 * L ^ 3 := by
    calc
      _ ≤ (38 * L ^ 2) * (20 * L) := mul_le_mul hA hBup hB (by positivity)
      _ = _ := by ring
  have hcoeff : (k + s) * (k + S) ≤ 4644 * L ^ 6 * Real.log L := by
    calc
      _ ≤ (k + s) * (258 * L ^ 4 * Real.log L) :=
        mul_le_mul_of_nonneg_left hkS (by linarith)
      _ ≤ (18 * L ^ 2) * (258 * L ^ 4 * Real.log L) :=
        mul_le_mul_of_nonneg_right hks (by positivity)
      _ = _ := by ring
  have hlower : L ^ 3 * Real.log L / 2 ≤ k * n / 2 := by
    have hnn : 0 ≤ n := (by positivity : 0 ≤ L ^ 2 * Real.log L).trans hn
    have h := mul_le_mul hk hn (by positivity : 0 ≤ L ^ 2 * Real.log L) hk0
    nlinarith
  have hmain' : L ^ 3 * Real.log L / 2 ≤
      760 * L ^ 3 + (4644 * L ^ 6 * Real.log L) * m := by
    exact hlower.trans (hmain.trans (add_le_add hcost (mul_le_mul_of_nonneg_right hcoeff hm)))
  have hquarter : 760 * L ^ 3 ≤ L ^ 3 * Real.log L / 4 := by
    have h := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ L ^ 3)
    nlinarith
  apply (div_le_iff₀ (show 0 < 18576 * L ^ 3 by positivity)).mpr
  apply (mul_le_mul_iff_right₀ (show 0 < L ^ 3 * Real.log L by positivity)).mp
  nlinarith [hmain', hquarter]

end OdlyzkoPoonen
