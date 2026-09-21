import OdlyzkoPoonen.ModFour.CompanionProbability
import OdlyzkoPoonen.Analysis.ResidueExponentialBound
import OdlyzkoPoonen.Analysis.FiniteExponentialExtension

/-!
# The companion event on the logarithmic exponential scale

The geometric companion estimate is stronger than a fixed logarithmic
exponential estimate. This form combines directly with the noncyclotomic
reciprocal-divisor estimate, uniformly down to degree three.
-/

namespace OdlyzkoPoonen

lemma logarithmic_exp_antitone_rate {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    Real.exp (-b * n / Real.log (n : ℝ) ^ 4) ≤
      Real.exp (-a * n / Real.log (n : ℝ) ^ 4) := by
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (neg_le_neg hab) (Nat.cast_nonneg n)) (by positivity)

lemma mod_four_companion_logarithmic_exponential_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      binaryProbability (n - 1) (HasModFourCompanion n) ≤
        C * Real.exp (-(1 / 32 : ℝ) * n / Real.log (n : ℝ) ^ 4) := by
  let f : ℕ → ℝ := fun n ↦ binaryProbability (n - 1) (HasModFourCompanion n) / 8
  obtain ⟨N, _, hscale⟩ := exists_threshold_logarithmic_prime_scale 1
  have hunit : ∀ n, f n ≤ 1 := by
    intro n
    have h := uniformProbability_le_one (fun w : Fin (n - 1) → Bool ↦
      HasModFourCompanion n (wordPolynomial w))
    dsimp [f, binaryProbability]
    linarith
  have he : ∀ n, max 8 N ≤ n →
      f n ≤ Real.exp (-(1 / 32 : ℝ) * n / Real.log (n : ℝ) ^ 4) := by
    intro n hn
    have hn8 : 8 ≤ n := (le_max_left _ _).trans hn
    have hlog := (hscale n ((le_max_right _ _).trans hn)).1
    have hk : (n : ℝ) / (4 * (2 : ℕ)) ≤ ((n - 1) / 4 : ℕ) := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4 * (2 : ℕ))).mpr
      exact_mod_cast (show n ≤ ((n - 1) / 4) * 8 by omega)
    have hgeom := three_quarters_pow_le_exp (n := n) (q := 2) (B := 2)
      (by norm_num) (by norm_num) hk
    have hr : (1 / 32 : ℝ) * n / Real.log (n : ℝ) ^ 4 ≤ (n : ℝ) / 32 := by
      have h := div_le_self (by positivity : (0 : ℝ) ≤ (1 / 32 : ℝ) * n)
        (one_le_pow₀ hlog : (1 : ℝ) ≤ Real.log (n : ℝ) ^ 4)
      nlinarith
    calc
      _ ≤ (3 / 4 : ℝ) ^ ((n - 1) / 4) := by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
        simpa only [mul_comm] using mod_four_companion_probability_le n (by omega)
      _ ≤ Real.exp (-(n : ℝ) / 32) := by norm_num at hgeom ⊢; exact hgeom
      _ ≤ _ := Real.exp_le_exp.mpr (by simpa only [neg_div, neg_mul] using neg_le_neg hr)
  obtain ⟨C, hC, hbound⟩ := extend_logarithmic_exponential_bound (by norm_num) hunit he
  refine ⟨8 * C, by positivity, ?_⟩
  intro n hn
  have h := (div_le_iff₀ (by norm_num : (0 : ℝ) < 8)).mp (hbound n hn)
  nlinarith

end OdlyzkoPoonen
