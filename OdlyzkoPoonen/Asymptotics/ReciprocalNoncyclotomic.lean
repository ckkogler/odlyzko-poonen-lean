import OdlyzkoPoonen.Analysis.ReciprocalCutoff
import OdlyzkoPoonen.Probability.ReciprocalNoncyclotomicFiniteBound

/-!
# Superpolynomial decay of reciprocal divisors without cyclotomic factors

This is Lemma 3.2 for the original fixed-endpoint binary law. Every positive
real decay exponent is allowed, with constants depending only on that exponent.
All arithmetic, finite counting and cutoff hypotheses are discharged.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics

lemma binaryProbability_reciprocal_noncyclotomic_isBigO (A : ℝ) (hA : 0 < A) :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun P ↦
      HasLargeReciprocalIntegerDivisor 1 P ∧ ¬ HasCyclotomicDivisor P)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-A)) := by
  obtain ⟨a, ha, N, _hN, hfinite⟩ := exists_noncyclotomic_reciprocal_finite_bound
  exact isBigO_rpow_of_reciprocal_finite_bound (fun _ ↦ uniformProbability_nonneg _)
    ha hfinite A hA

end OdlyzkoPoonen
