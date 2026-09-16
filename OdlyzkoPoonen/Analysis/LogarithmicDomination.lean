import OdlyzkoPoonen.Analysis.LogarithmicScale

/-!
# Linear growth dominates products of logarithmic powers

A fixed multiple of any logarithmic power is eventually bounded by a positive
multiple of the degree divided by any other logarithmic power. The constants
are fixed before the degree threshold is chosen.
-/

namespace OdlyzkoPoonen
open Filter
open scoped Topology

lemma eventually_log_pow_le_nat_div_log_pow (B : ℝ) {a : ℝ} (ha : 0 < a) (r s : ℕ) :
    ∀ᶠ n : ℕ in atTop, B * Real.log (n : ℝ) ^ r ≤
      a * (n : ℝ) / Real.log (n : ℝ) ^ s := by
  have ht : Tendsto (fun n : ℕ ↦ B * Real.log (n : ℝ) ^ (r + s) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using (tendsto_log_nat_pow_div_nat (r + s)).const_mul B
  filter_upwards [eventually_ge_atTop 2, ht.eventually_le_const ha] with n hn hsmall
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  apply (le_div_iff₀ (pow_pos hlog s)).mpr
  rw [mul_assoc, ← pow_add]
  exact (div_le_iff₀ hn0).mp hsmall

end OdlyzkoPoonen
