import OdlyzkoPoonen.Probability.BernoulliCount
import OdlyzkoPoonen.Polynomial.MinusOneEvaluation
import OdlyzkoPoonen.Asymptotics.CentralBinomial
import OdlyzkoPoonen.Analysis.SquareRootComparison

/-!
# Uniform bounds on atoms of sums of fair bits

Enlarging a word to the next even length changes normalization by at most two.
The central binomial bound therefore gives the uniform estimate
`4/sqrt(m+1)`, including length zero and target values outside the support.
Integer targets and deterministic shifts are allowed for later residue sums.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma uniformProbability_trueBitCount_le_central {m r : ℕ}
    (hm : m ≤ 2 * r) (hr : 2 * r ≤ m + 1) (k : ℕ) :
    uniformProbability (fun w : Fin m → Bool ↦ trueBitCount w = k) ≤
      2 * centralBinomialMass r := by
  have hc : m.choose k ≤ Nat.centralBinom r :=
    (Nat.choose_le_choose k hm).trans (Nat.choose_le_centralBinom k r)
  have hp : (2 : ℝ) ^ (2 * r) ≤ 2 * (2 : ℝ) ^ m := by
    calc
      (2 : ℝ) ^ (2 * r) ≤ 2 ^ (m + 1) := by gcongr; norm_num
      _ = 2 * (2 : ℝ) ^ m := by rw [pow_succ]; ring
  rw [uniformProbability_trueBitCount]
  calc
    _ ≤ (Nat.centralBinom r : ℝ) / (2 : ℝ) ^ m := by gcongr
    _ ≤ (2 * (Nat.centralBinom r : ℝ)) / (2 : ℝ) ^ (2 * r) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have h := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (Nat.centralBinom r))
      nlinarith
    _ = 2 * centralBinomialMass r := by
      rw [centralBinomialMass_eq_choose, Nat.centralBinom_eq_two_mul_choose]
      ring

lemma uniformProbability_trueBitCount_le_sqrt (m k : ℕ) :
    uniformProbability (fun w : Fin m → Bool ↦ trueBitCount w = k) ≤
      4 / Real.sqrt ((m : ℝ) + 1) := by
  by_cases hm : m = 0
  · subst m
    calc
      _ ≤ 1 := uniformProbability_le_one _
      _ ≤ _ := by norm_num
  let r := (m + 1) / 2
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hmr : m ≤ 2 * r := by dsimp [r]; omega
  have hrm : 2 * r ≤ m + 1 := by dsimp [r]; omega
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hm1 : 0 < (m : ℝ) + 1 := by positivity
  have hms : Real.sqrt ((m : ℝ) + 1) ≤ 2 * Real.sqrt (r : ℝ) := by
    have he : (m : ℝ) + 1 ≤ 4 * (r : ℝ) := by exact_mod_cast (show m + 1 ≤ 4 * r by omega)
    have h₁ := Real.sq_sqrt hm1.le
    have h₂ := Real.sq_sqrt hr0.le
    have h₃ := Real.sqrt_nonneg ((m : ℝ) + 1)
    have h₄ := Real.sqrt_nonneg (r : ℝ)
    nlinarith
  calc
    _ ≤ 2 * centralBinomialMass r := uniformProbability_trueBitCount_le_central hmr hrm k
    _ ≤ 2 * (1 / Real.sqrt (Real.pi * (r : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (centralBinomialMass_le_sqrt hr) (by norm_num)
    _ ≤ 2 / Real.sqrt (r : ℝ) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (inverse_sqrt_pi_le hr0) (by norm_num : (0 : ℝ) ≤ 2)
    _ ≤ 4 / Real.sqrt ((m : ℝ) + 1) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith

lemma uniformProbability_bitValue_sum_le (m : ℕ) (z : ℤ) :
    uniformProbability (fun w : Fin m → Bool ↦ (∑ i, bitValue (w i)) = z) ≤
      4 / Real.sqrt ((m : ℝ) + 1) := by
  calc
    _ ≤ uniformProbability (fun w : Fin m → Bool ↦ trueBitCount w = z.toNat) := by
      apply uniformProbability_mono
      intro w hw
      rw [sum_bitValue_eq_trueBitCount] at hw
      simpa only [Int.toNat_natCast] using congrArg Int.toNat hw
    _ ≤ _ := uniformProbability_trueBitCount_le_sqrt m z.toNat

lemma uniformProbability_shifted_bitValue_sum_le (m : ℕ) (a z : ℤ) :
    uniformProbability (fun w : Fin m → Bool ↦ a + ∑ i, bitValue (w i) = z) ≤
      4 / Real.sqrt ((m : ℝ) + 1) := by
  calc
    _ ≤ uniformProbability (fun w : Fin m → Bool ↦ (∑ i, bitValue (w i)) = z - a) := by
      apply uniformProbability_mono
      intro w hw
      omega
    _ ≤ _ := uniformProbability_bitValue_sum_le m (z - a)

end OdlyzkoPoonen
