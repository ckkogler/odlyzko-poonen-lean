import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Integer quotient bounds for the number of exposed bits

The exact number of selected internal positions is a natural quotient. These
lemmas control the loss from rounding and convert its fair-bit mass to the
fourth-power logarithmic exponential rate.
-/

namespace OdlyzkoPoonen

lemma nat_div_ge_half_real_ratio {m q : ℕ} (hq : 0 < q) (hqm : q ≤ m) :
    (m : ℝ) / (2 * (q : ℝ)) ≤ ((m / q : ℕ) : ℝ) := by
  have hk : 1 ≤ m / q := Nat.div_pos hqm hq
  have hkR : (1 : ℝ) ≤ (m / q : ℕ) := by exact_mod_cast hk
  have hr : ((m % q : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast Nat.mod_lt m hq
  have he : ((m % q : ℕ) : ℝ) + (q : ℝ) * ((m / q : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast Nat.mod_add_div m q
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqk : (q : ℝ) ≤ (q : ℝ) * ((m / q : ℕ) : ℝ) :=
    le_mul_of_one_le_right hqR.le hkR
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
  nlinarith

lemma sparse_quotient_lower {n q : ℕ} (hn : 2 ≤ n) (hq : 0 < q)
    (hqm : q ≤ n - 1) {K : ℝ} (hK : 0 < K) (hlog : 1 ≤ Real.log (n : ℝ))
    (hqupper : (q : ℝ) ≤ 16 * K * Real.log (n : ℝ) ^ 4) :
    (n : ℝ) / (64 * K * Real.log (n : ℝ) ^ 4) ≤ (((n - 1) / q : ℕ) : ℝ) := by
  have hlog0 : 0 < Real.log (n : ℝ) := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (n : ℝ) / 2 ≤ ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    linarith
  calc
    _ = ((n : ℝ) / 2) / (2 * (16 * K * Real.log (n : ℝ) ^ 4)) := by ring
    _ ≤ ((n - 1 : ℕ) : ℝ) / (2 * (16 * K * Real.log (n : ℝ) ^ 4)) :=
      div_le_div_of_nonneg_right hm (by positivity)
    _ ≤ ((n - 1 : ℕ) : ℝ) / (2 * (q : ℝ)) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left hqupper (by norm_num))
    _ ≤ _ := nat_div_ge_half_real_ratio hq hqm

lemma half_pow_sparse_quotient_le_exp {n q : ℕ} (hn : 2 ≤ n) (hq : 0 < q)
    (hqm : q ≤ n - 1) {K : ℝ} (hK : 0 < K) (hlog : 1 ≤ Real.log (n : ℝ))
    (hqupper : (q : ℝ) ≤ 16 * K * Real.log (n : ℝ) ^ 4) :
    (1 / 2 : ℝ) ^ ((n - 1) / q) ≤
      Real.exp (-(Real.log 2 / (64 * K)) * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
  have hcount := sparse_quotient_lower hn hq hqm hK hlog hqupper
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  calc
    _ = Real.exp ((((n - 1) / q : ℕ) : ℝ) * Real.log (1 / 2 : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ = Real.exp (-((((n - 1) / q : ℕ) : ℝ) * Real.log 2)) := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      congr 1
      ring
    _ ≤ Real.exp (-((n : ℝ) / (64 * K * Real.log (n : ℝ) ^ 4) * Real.log 2)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_right hcount hlog2.le)
    _ = _ := by congr 1; ring

end OdlyzkoPoonen
