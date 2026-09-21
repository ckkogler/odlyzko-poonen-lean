import OdlyzkoPoonen.Probability.WordPairConcentration

/-!
# Concentration at a fourth-power logarithmic scale

For `T=K*(log n)^4` with fixed `K>=3`, the explicit prime-union concentration
bound is eventually at most `exp(-n/(256T))`. The threshold depends only on K.
-/

namespace OdlyzkoPoonen

theorem logarithmic_opposite_prime_pairs_concentration {K : ℝ} (hK : 3 ≤ K) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      uniformProbability (fun w : Fin (n - 1) → Bool ↦
        HasSparseOppositePrimePairs n (K * Real.log (n : ℝ) ^ 4) (oppositePairMask w)) ≤
          Real.exp (-(n : ℝ) / (256 * (K * Real.log (n : ℝ) ^ 4))) := by
  have hK0 : 0 < K := by linarith
  obtain ⟨N₀, _, hscale⟩ := exists_threshold_logarithmic_prime_scale K
  obtain ⟨N₁, _, habsorb⟩ := exists_threshold_absorb_quadratic_logarithmic_exp
    (show 0 < 1 / (128 * K) by positivity)
  refine ⟨max 3 (max N₀ N₁), le_max_left _ _, ?_⟩
  intro n hn
  have hn3 : 3 ≤ n := (le_max_left _ _).trans hn
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₁ : N₁ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  obtain ⟨hlog, hsmall⟩ := hscale n hn₀
  let T := K * Real.log (n : ℝ) ^ 4
  have hT : 2 ≤ T := by
    have hpow : (1 : ℝ) ≤ Real.log (n : ℝ) ^ 4 := one_le_pow₀ hlog
    dsimp [T]
    nlinarith
  have hsmall' : 64 * T ≤ (n : ℝ) := by dsimp [T]; nlinarith
  have hne : 8 * T ≤ (n : ℝ) := by linarith
  calc
    _ ≤ 2 * T * Real.exp (-(n : ℝ) / (128 * T)) :=
      word_opposite_prime_pairs_concentration hT hne
    _ ≤ (n : ℝ) ^ 2 * Real.exp (-(n : ℝ) / (128 * T)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith
    _ = (n : ℝ) ^ 2 * Real.exp (-(1 / (128 * K)) * n / Real.log (n : ℝ) ^ 4) := by
      congr 2
      dsimp [T]
      ring
    _ ≤ Real.exp (-((1 / (128 * K)) / 2) * n / Real.log (n : ℝ) ^ 4) := habsorb n hn₁
    _ = _ := by congr 1; ring

end OdlyzkoPoonen
