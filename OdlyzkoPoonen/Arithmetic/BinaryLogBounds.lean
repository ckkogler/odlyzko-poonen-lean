import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Integer binary logarithms and real logarithmic growth

The integer logarithm gives a cutoff with exact power inequalities. Its upper
comparison with the real logarithm follows by taking logarithms of the proved
integer inequality `2^(log_2 n) ≤ n`. This avoids any unproved rounding rule.
-/

namespace OdlyzkoPoonen

lemma natLog_two_le_real_log_div {n : ℕ} (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hp : (2 : ℝ) ^ Nat.log 2 n ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ Nat.log 2 n) hp
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr hl

lemma nat_pow_le_two_pow_log_multiple (n a : ℕ) :
    n ^ a ≤ 2 ^ (a * (Nat.log 2 n + 1)) := by
  have h : n ≤ 2 ^ (Nat.log 2 n + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n).le
  calc
    _ ≤ (2 ^ (Nat.log 2 n + 1)) ^ a := Nat.pow_le_pow_left h a
    _ = _ := by rw [← pow_mul, Nat.mul_comm]

end OdlyzkoPoonen
