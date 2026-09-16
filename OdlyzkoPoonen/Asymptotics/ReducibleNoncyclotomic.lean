import OdlyzkoPoonen.Analysis.GeometricQuotientDecay
import OdlyzkoPoonen.Asymptotics.ReciprocalNoncyclotomic
import OdlyzkoPoonen.Reducibility.EventBounds

/-!
# Reducibility without cyclotomic factors is superpolynomially rare

The companion bound and Lemma 3.2 combine under the actual finite probability
law. This proves (3.3) for every positive real decay exponent.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics

lemma binaryProbability_companion_isBigO (A : ℝ) :
    (fun n : ℕ ↦ binaryProbability (n - 1) (HasModFourCompanion n)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
  have h := (geometric_quarter_isBigO_rpow (by norm_num : (0 : ℝ) < 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) A).const_mul_left 8
  refine (Asymptotics.IsBigO.of_norm_eventuallyLE ?_).trans h
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp0 : 0 ≤ binaryProbability (n - 1) (HasModFourCompanion n) := uniformProbability_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp0,
    abs_of_nonneg (show (0 : ℝ) ≤ 8 * (3 / 4 : ℝ) ^ ((n - 1) / 4) by positivity)]
    using mod_four_companion_probability_le n hn

lemma binaryProbability_reducible_noncyclotomic_isBigO (A : ℝ) (hA : 0 < A) :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun P ↦
      ReducibleOverRat P ∧ ¬ HasCyclotomicDivisor P)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
  have h := (binaryProbability_companion_isBigO A).add
    (binaryProbability_reciprocal_noncyclotomic_isBigO A hA)
  refine (Asymptotics.IsBigO.of_norm_eventuallyLE ?_).trans h
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hprob := reducible_without_cyclotomic_probability_le hn
  have hnonneg : 0 ≤ binaryProbability (n - 1) (fun P ↦
      ReducibleOverRat P ∧ ¬ HasCyclotomicDivisor P) := uniformProbability_nonneg _
  have hsum : 0 ≤ binaryProbability (n - 1) (HasModFourCompanion n) +
      binaryProbability (n - 1) (fun P ↦
        HasLargeReciprocalIntegerDivisor 1 P ∧ ¬ HasCyclotomicDivisor P) :=
    add_nonneg (uniformProbability_nonneg _) (uniformProbability_nonneg _)
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hsum] using hprob

end OdlyzkoPoonen
