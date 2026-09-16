import OdlyzkoPoonen.Analysis.ChebyshevInterval
import OdlyzkoPoonen.Arithmetic.PrimeIntervals

/-!
# Exponential growth of the prime product on a fixed-ratio interval

There is one absolute threshold beyond which the product of all primes in
`(n, 8n]` is at least `exp n`. The final lemma selects a prime in that interval
which does not divide a given positive integer smaller than `exp n`.
-/

namespace OdlyzkoPoonen
open Filter

lemma eventually_exp_le_primeIntervalProduct :
    ∀ᶠ n : ℕ in atTop, Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ) := by
  filter_upwards [eventually_theta_eight_mul_sub_ge.natCast_atTop] with n hn
  have hp : (0 : ℝ) < (primeIntervalProduct n (8 * n) : ℝ) :=
    Nat.cast_pos.mpr (primeIntervalProduct_pos _ _)
  apply (Real.exp_le_exp.mpr ?_).trans_eq (Real.exp_log hp)
  rw [log_primeIntervalProduct (by omega : n ≤ 8 * n)]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn

lemma exists_threshold_exp_le_primeIntervalProduct :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp eventually_exp_le_primeIntervalProduct
  exact ⟨max 1 n₀, le_max_left _ _, fun n hn ↦ hn₀ n ((le_max_right _ _).trans hn)⟩

lemma exists_prime_in_interval_not_dvd_of_log_lt {n B : ℕ} (hB : 0 < B)
    (hgrowth : Real.exp (n : ℝ) ≤ (primeIntervalProduct n (8 * n) : ℝ))
    (hlog : Real.log (B : ℝ) < (n : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 8 * n ∧ ¬ p ∣ B := by
  apply exists_prime_in_interval_not_dvd hB
  have hBpos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have hlt : (B : ℝ) < (primeIntervalProduct n (8 * n) : ℝ) := by
    calc
      _ = Real.exp (Real.log (B : ℝ)) := (Real.exp_log hBpos).symm
      _ < Real.exp (n : ℝ) := Real.exp_lt_exp.mpr hlog
      _ ≤ _ := hgrowth
  exact_mod_cast hlt

end OdlyzkoPoonen
