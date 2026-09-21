import OdlyzkoPoonen.Probability.CyclotomicDegreeRange
import OdlyzkoPoonen.Asymptotics.CyclotomicCutoff

/-!
# Cyclotomic truncation to arbitrary polynomial accuracy

For every natural accuracy parameter `R`, the probability of a cyclotomic
divisor of degree at least `2*R+1` is `O(n^(-R))`. A scaled logarithmic cutoff
controls the very large degrees, while the residue atom estimate controls
the intervening degrees. The retained degree bound is independent of `n`.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics
open scoped Topology Classical

def scaledCyclotomicCutoff (c n : ℕ) : ℕ := c * cyclotomicDegreeCutoff n

lemma scaledCyclotomicCutoff_isBigO_log (c : ℕ) :
    (fun n : ℕ ↦ (scaledCyclotomicCutoff c n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  simpa only [scaledCyclotomicCutoff, Nat.cast_mul] using
    cyclotomicDegreeCutoff_isBigO_log.const_mul_left (c : ℝ)

lemma scaledCyclotomicCutoff_pow_isLittleO_sqrt (c d : ℕ) :
    (fun n : ℕ ↦ (scaledCyclotomicCutoff c n : ℝ) ^ d) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) :=
  ((scaledCyclotomicCutoff_isBigO_log c).pow d).trans_isLittleO
    (log_nat_pow_isLittleO_sqrt d)

lemma eventually_scaledCyclotomicCutoff_pow_le_sqrt (c d : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (scaledCyclotomicCutoff c n : ℝ) ^ d ≤ Real.sqrt (n : ℝ) := by
  have h := (scaledCyclotomicCutoff_pow_isLittleO_sqrt c d).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h] with n hn
  have hpow0 : (0 : ℝ) ≤ (scaledCyclotomicCutoff c n : ℝ) ^ d := by positivity
  simpa only [one_mul, Real.norm_eq_abs,
    abs_of_nonneg hpow0,
    abs_of_nonneg (Real.sqrt_nonneg _)] using hn

lemma eventually_scaledCyclotomicCutoff_scale_le_one (c : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      8 * (scaledCyclotomicCutoff c n : ℝ) / Real.sqrt (n : ℝ) ≤ 1 := by
  have ht : Tendsto
      (fun n : ℕ ↦ 8 * (scaledCyclotomicCutoff c n : ℝ) / Real.sqrt (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero, mul_div_assoc] using
      ((scaledCyclotomicCutoff_pow_isLittleO_sqrt c 1).tendsto_div_nhds_zero).const_mul 8
  exact ht.eventually_le_const (by norm_num : (0 : ℝ) < 1)

lemma nat_pow_le_two_pow_scaledCyclotomicCutoff (c n : ℕ) :
    (n : ℝ) ^ (8 * c) ≤ (2 : ℝ) ^ scaledCyclotomicCutoff c n := by
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 8)
    (pow_eight_le_two_pow_cyclotomicDegreeCutoff n) c
  simpa only [← pow_mul, scaledCyclotomicCutoff, Nat.mul_comm] using h

lemma cyclotomic_middle_scaled_bound {n L R : ℕ} (hn : 1 ≤ n)
    (hL : (L : ℝ) ^ (2 * R + 3) ≤ Real.sqrt (n : ℝ)) :
    (2 * (L : ℝ) ^ 2 * (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ (2 * R + 1)) *
      (n : ℝ) ^ R ≤ 2 * (8 : ℝ) ^ (2 * R + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hden : Real.sqrt (n : ℝ) ^ (2 * R + 1) =
      (n : ℝ) ^ R * Real.sqrt (n : ℝ) := by
    rw [pow_succ, pow_mul, hs2]
  have he : (2 * (L : ℝ) ^ 2 * (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ (2 * R + 1)) *
      (n : ℝ) ^ R =
      (2 * (8 : ℝ) ^ (2 * R + 1)) * ((L : ℝ) ^ (2 * R + 3) / Real.sqrt (n : ℝ)) := by
    rw [div_pow, mul_pow, hden, show 2 * R + 3 = (2 * R + 1) + 2 by omega,
      pow_add]
    field_simp
    ring
  rw [he]
  have hdiv : (L : ℝ) ^ (2 * R + 3) / Real.sqrt (n : ℝ) ≤ 1 :=
    (div_le_one hs).mpr hL
  nlinarith [show (0 : ℝ) ≤ 2 * 8 ^ (2 * R + 1) by positivity]

lemma cyclotomic_high_scaled_bound {n R : ℕ} (hn : 1 ≤ n) :
    (4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ scaledCyclotomicCutoff (R + 1) n) *
      (n : ℝ) ^ R ≤ 4 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (R + 2) ≤ (2 : ℝ) ^ scaledCyclotomicCutoff (R + 1) n := by
    apply le_trans _ (nat_pow_le_two_pow_scaledCyclotomicCutoff (R + 1) n)
    exact pow_le_pow_right₀ hnR (by omega)
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc
    _ = 4 * (n : ℝ) ^ (R + 2) := by rw [pow_add]; ring
    _ ≤ _ := by gcongr

/-- Cyclotomic degrees above a fixed threshold have any prescribed inverse
polynomial decay. The threshold depends only on the requested accuracy. -/
theorem binaryProbability_cyclotomic_degree_tail_isBigO (R : ℕ) :
    (fun n : ℕ ↦ binaryProbability (n - 1)
      (fun p ↦ ∃ k, 2 * R + 1 ≤ k.totient ∧ cyclotomic k ℤ ∣ p)) =O[atTop]
      (fun n : ℕ ↦ ((n : ℝ) ^ R)⁻¹) := by
  refine isBigO_iff.mpr ⟨2 * (8 : ℝ) ^ (2 * R + 1) + 4, ?_⟩
  filter_upwards [eventually_ge_atTop 1,
    eventually_scaledCyclotomicCutoff_pow_le_sqrt (R + 1) (2 * R + 3),
    eventually_scaledCyclotomicCutoff_scale_le_one (R + 1)] with n hn hL hsmall
  have h := binaryProbability_cyclotomic_degree_at_least_le hn
    (show 1 ≤ 2 * R + 1 by omega) hsmall
  have hm := cyclotomic_middle_scaled_bound (R := R) hn hL
  have hh := cyclotomic_high_scaled_bound (R := R) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hprod := mul_le_mul_of_nonneg_right h (pow_nonneg hn0.le R)
  have hp0 : 0 ≤ binaryProbability (n - 1)
      (fun p ↦ ∃ k, 2 * R + 1 ≤ k.totient ∧ cyclotomic k ℤ ∣ p) :=
    uniformProbability_nonneg _
  simp only [Real.norm_eq_abs, abs_of_nonneg hp0,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hn0.le R))]
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hn0 R)]
  nlinarith

end OdlyzkoPoonen
