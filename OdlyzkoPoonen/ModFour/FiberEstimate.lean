import OdlyzkoPoonen.ModFour.DiscrepancyLocality
import OdlyzkoPoonen.ModFour.ExposureToggle
import OdlyzkoPoonen.FiniteField.PairedUpdate
import OdlyzkoPoonen.FiniteField.PairSums
import OdlyzkoPoonen.Probability.AverageBounds

/-!
# The discrepancy estimate on actual polynomial fibers

Fix the first factor and the opposite-pair sums of the second factor. The
active coefficients are precisely those where the toggle slope is one. Each
active discrepancy consumes one fresh fair lower bit, so requiring all exposed
discrepancies to vanish has probability at most `2` to the negative number of
active indices. The proof establishes both locality and toggling for the actual
polynomials; neither is an extra hypothesis. Averaging over the optional center
and pair sums gives an estimate for the original uniform polynomial family.
-/

namespace OdlyzkoPoonen
open Polynomial

/-- Active exposed positions: the actual coefficient of `(a+a.reverse)c` is one. -/
noncomputable def activeDiscrepancyIndices {n : ℕ} (a : (ZMod 2)[X])
    (c : Fin (n / 2) → Bool) : Finset (Fin (n / 2)) :=
  Finset.univ.filter (fun i ↦ ((a + a.reverse) * pairSumPolynomial c).coeff (i.val + 1) = 1)

lemma pairedDiscrepancy_togglesOn {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (c : Fin (n / 2) → Bool) (z : Fin (n % 2) → Bool) :
    TogglesOn (activeDiscrepancyIndices a c) (pairedDiscrepancy a c z) := by
  classical
  intro i hi u
  have hi1 : ((a + a.reverse) * pairSumPolynomial c).coeff (i.val + 1) = 1 :=
    (Finset.mem_filter.mp hi).2
  have ht := autocorrelationDiscrepancy_togglePair ha (pairedPolynomial_endpoints u c z)
    (show 0 < i.val + 1 by omega) (show 2 * (i.val + 1) < n + 1 by have := i.isLt; omega)
  rw [paired_sum_reverse_eq_pairSumPolynomial, hi1] at ht
  have heq := (sub_eq_iff_eq_add.mp ht).trans (add_comm _ _)
  simp only [pairedDiscrepancy, pairedPolynomial_update, heq, f2ToBit_add_one]

/-- Finite counting form of the fresh-discrepancy estimate, at fixed pair sums
and any fixed central word. This is the coefficient-event bound itself. -/
lemma paired_discrepancies_zero_probability_le {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (c : Fin (n / 2) → Bool) (z : Fin (n % 2) → Bool) :
    uniformProbability (fun u : Fin (n / 2) → Bool ↦
      ∀ i : Fin (n / 2),
        autocorrelationDiscrepancy a (pairedPolynomial u c z) (i.val + 1) = 0) ≤
      (1 / 2 : ℝ) ^ (activeDiscrepancyIndices a c).card := by
  have h := uniformProbability_all_outputs_zero_le
    (pairedDiscrepancy_dependsOnPrefix ha c z) (pairedDiscrepancy_togglesOn ha c z)
  simpa only [pairedDiscrepancy, f2ToBit_eq_false_iff] using h

/-- The full fiber over fixed pair sums includes a uniformly chosen center.
The word-coordinate bijection identifies this product law with the actual
fiber of the original polynomial family. -/
lemma paired_discrepancies_zero_fiber_probability_le {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (c : Fin (n / 2) → Bool) :
    uniformProbability (fun v : (Fin (n % 2) → Bool) × (Fin (n / 2) → Bool) ↦
      ∀ i : Fin (n / 2),
        autocorrelationDiscrepancy a (pairedPolynomial v.2 c v.1) (i.val + 1) = 0) ≤
      (1 / 2 : ℝ) ^ (activeDiscrepancyIndices a c).card := by
  rw [uniformProbability_product_eq_average
    (fun (z : Fin (n % 2) → Bool) (u : Fin (n / 2) → Bool) ↦
      ∀ i : Fin (n / 2),
        autocorrelationDiscrepancy a (pairedPolynomial u c z) (i.val + 1) = 0)]
  exact uniformAverage_le (fun z ↦ paired_discrepancies_zero_probability_le ha c z)

/-- Modulo-four agreement imposes all the exposed zero-discrepancy constraints. -/
lemma paired_factor_congruence_probability_le {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (c : Fin (n / 2) → Bool) (z : Fin (n % 2) → Bool) :
    uniformProbability (fun u : Fin (n / 2) → Bool ↦
      CongruentMod 4 (autocorrelation (zeroOneLift (a * pairedPolynomial u c z)))
        (autocorrelation (zeroOneLift (a * (pairedPolynomial u c z).reverse)))) ≤
      (1 / 2 : ℝ) ^ (activeDiscrepancyIndices a c).card := by
  apply le_trans (uniformProbability_mono (fun u h i ↦ ?_))
    (paired_discrepancies_zero_probability_le ha c z)
  have hb : (pairedPolynomial u c z).coeff 0 ≠ 0 := by
    rw [(pairedPolynomial_endpoints u c z).constant]
    exact one_ne_zero
  exact (lifted_factor_congruent_four_iff a _ hb).mp h (i.val + 1)

/-- The original uniform polynomial law, bounded by the average active weight. -/
lemma f2_factor_congruence_probability_le_average {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) :
    f2Probability n (fun b ↦
      CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
        (autocorrelation (zeroOneLift (a * b.reverse)))) ≤
      uniformAverage (fun c : Fin (n / 2) → Bool ↦
        (1 / 2 : ℝ) ^ (activeDiscrepancyIndices a c).card) := by
  rw [f2Probability_eq_paired_average]
  apply uniformAverage_mono
  intro c
  exact uniformAverage_le (fun z ↦ paired_factor_congruence_probability_le ha c z)

end OdlyzkoPoonen
