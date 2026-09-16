import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Numerical estimates for the sparse Mahler argument

A fourth-power logarithmic prime scale satisfies the root-separation threshold
and amplifies the cubic logarithmic Mahler gap past the ambient degree.
-/

namespace OdlyzkoPoonen

lemma logarithmic_prime_scale_ge {C K L D : ℝ} (hC : 0 ≤ C) (hK : 2 * C ≤ K)
    (hL : 1 ≤ L) (hD : D ≤ L) : C * (1 + D) ≤ K * L ^ 4 := by
  have hK0 : 0 ≤ K := by linarith
  calc
    C * (1 + D) ≤ C * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) hC
    _ = (2 * C) * L := by ring
    _ ≤ K * L := mul_le_mul_of_nonneg_right hK (by linarith)
    _ ≤ K * L ^ 4 := mul_le_mul_of_nonneg_left
      (by simpa using pow_le_pow_right₀ hL (show 1 ≤ 4 by norm_num)) hK0

lemma log_lt_prime_mul_log_of_mahler_gap {c K L M : ℝ} (hc : 0 < c)
    (hK : 1 / c ≤ K) (hL : 1 ≤ L) {q : ℕ} (hq : K * L ^ 4 < (q : ℝ))
    (hM : c / L ^ 3 ≤ Real.log M) : L < (q : ℝ) * Real.log M := by
  have hL0 : 0 < L := by linarith
  have hKc : 1 ≤ K * c := (div_le_iff₀ hc).mp hK
  have heq : (K * L ^ 4) * (c / L ^ 3) = (K * c) * L := by
    field_simp
  calc
    L ≤ (K * c) * L := by nlinarith
    _ = (K * L ^ 4) * (c / L ^ 3) := heq.symm
    _ < (q : ℝ) * (c / L ^ 3) := mul_lt_mul_of_pos_right hq (by positivity)
    _ ≤ (q : ℝ) * Real.log M := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg _)

end OdlyzkoPoonen
