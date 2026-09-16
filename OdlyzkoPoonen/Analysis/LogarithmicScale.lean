import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Logarithmic scales are smaller than the ambient degree

These elementary asymptotic bounds choose an absolute degree threshold once
its constant is fixed. They justify the prime scale in the sparse-bit argument.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics Real
open scoped Topology

lemma log_nat_pow_isLittleO_nat (d : ℕ) :
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ d) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  have h := (isLittleO_log_rpow_rpow_atTop (d : ℝ)
    (by norm_num : (0 : ℝ) < 1)).comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  simpa only [Function.comp_def, Real.rpow_natCast, Real.rpow_one] using h

lemma tendsto_log_nat_pow_div_nat (d : ℕ) :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ d / (n : ℝ)) atTop (𝓝 0) :=
  (log_nat_pow_isLittleO_nat d).tendsto_div_nhds_zero

lemma exists_threshold_logarithmic_prime_scale (K : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      1 ≤ Real.log (n : ℝ) ∧ 64 * K * Real.log (n : ℝ) ^ 4 ≤ (n : ℝ) := by
  have ht : Tendsto (fun n : ℕ ↦ 64 * K * Real.log (n : ℝ) ^ 4 / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using (tendsto_log_nat_pow_div_nat 4).const_mul (64 * K)
  have hl : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧
      64 * K * Real.log (n : ℝ) ^ 4 ≤ (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2, hl.eventually_ge_atTop 1,
      ht.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with n hn hlog hsmall
    refine ⟨hn, hlog, ?_⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    simpa only [one_mul] using (div_le_iff₀ hn0).mp hsmall
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  exact ⟨max 2 N, le_max_left _ _, fun n hn ↦ (hN n ((le_max_right _ _).trans hn)).2⟩

end OdlyzkoPoonen
