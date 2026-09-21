import OdlyzkoPoonen.Analysis.LogarithmicScale

/-!
# Exponential bounds for selected residue pairs

The exact geometric weight yields a degree-over-modulus exponential. A fixed
quadratic prefactor can then be absorbed in the logarithmic exponential scale.
-/

namespace OdlyzkoPoonen
open Filter

lemma three_quarters_pow_le_exp {n q k : ℕ} {B : ℝ}
    (hq : 0 < q) (hB : (q : ℝ) ≤ B) (hk : (n : ℝ) / (4 * q) ≤ k) :
    (3 / 4 : ℝ) ^ k ≤ Real.exp (-(n : ℝ) / (16 * B)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hb : (3 / 4 : ℝ) ≤ Real.exp (-(1 / 4)) := by
    have h := Real.add_one_le_exp (-(1 / 4 : ℝ))
    linarith
  have hrate : (n : ℝ) / (16 * B) ≤ (k : ℝ) / 4 := by
    calc
      _ ≤ (n : ℝ) / (16 * q) := div_le_div_of_nonneg_left (Nat.cast_nonneg n)
        (by positivity) (by linarith)
      _ = ((n : ℝ) / (4 * q)) / 4 := by rw [div_div]; congr 1; ring
      _ ≤ _ := div_le_div_of_nonneg_right hk (by norm_num)
  calc
    _ ≤ Real.exp (-(1 / 4 : ℝ)) ^ k := pow_le_pow_left₀ (by norm_num) hb _
    _ = Real.exp (-(k : ℝ) / 4) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hrate)

lemma exists_threshold_absorb_quadratic_logarithmic_exp {a : ℝ} (ha : 0 < a) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ 2 * Real.exp (-a * n / Real.log (n : ℝ) ^ 4) ≤
        Real.exp (-(a / 2) * n / Real.log (n : ℝ) ^ 4) := by
  have he := (tendsto_log_nat_pow_div_nat 5).eventually_le_const
    (show (0 : ℝ) < a / 4 by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := lt_trans zero_lt_one hnR
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hsmall := (div_le_iff₀ hn0).mp (hN n ((le_max_right _ _).trans hn))
  have hrate : 2 * Real.log (n : ℝ) ≤ (a / 2) * n / Real.log (n : ℝ) ^ 4 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have heq : (n : ℝ) ^ 2 = Real.exp (2 * Real.log (n : ℝ)) := by
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hn0]
  rw [heq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (a / 2) * n / Real.log (n : ℝ) ^ 4 + -a * n / Real.log (n : ℝ) ^ 4 :=
      add_le_add hrate le_rfl
    _ = _ := by ring

end OdlyzkoPoonen
