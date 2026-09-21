import OdlyzkoPoonen.Probability.ReciprocalIntegerDivisors

/-!
# The reciprocal integer-divisor degree tail

Every monic reciprocal integer divisor contributes its degree to the gcd after
reduction modulo two. The stronger coefficient-six estimate gives the convenient
coefficient-eight version for every natural cutoff.
-/

namespace OdlyzkoPoonen

theorem binaryProbability_large_reciprocal_divisor_le_eight {n : ℕ}
    (hn : 1 ≤ n) (L : ℕ) :
    binaryProbability (n - 1) (HasLargeReciprocalIntegerDivisor L) ≤
      8 * (2 : ℝ) ^ (-(L : ℝ) / 2) := by
  refine (binaryProbability_large_reciprocal_divisor_le hn L).trans ?_
  exact mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg (by norm_num) _)

end OdlyzkoPoonen
