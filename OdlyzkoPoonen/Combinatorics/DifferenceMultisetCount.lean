import OdlyzkoPoonen.Combinatorics.AutocorrelationCount
import OdlyzkoPoonen.Combinatorics.ImageCardinality
import OdlyzkoPoonen.Polynomial.BinarySets
import OdlyzkoPoonen.Polynomial.DifferenceMultiset

/-!
# Finite bounds for distinct difference multisets

The family consists of the signed difference multisets of subsets of
`{0, ..., n}` containing both endpoints. Repeated values are counted once.
The bounds retain the exact exponential error and reversal correction.
-/

namespace OdlyzkoPoonen

/-- Distinct signed difference multisets of endpoint-fixed subsets. -/
noncomputable def differenceMultisetFamily (n : ℕ) : Finset (Multiset ℤ) :=
  (binarySetFamily n).image differenceMultiset

theorem card_differenceMultisetFamily {n : ℕ} (hn : 1 ≤ n) :
    (differenceMultisetFamily n).card = (binaryAutocorrelationFamily (n - 1)).card := by
  classical
  rw [differenceMultisetFamily, binaryAutocorrelationFamily,
    ← binarySetFamily_image_setPolynomial hn, Finset.image_image]
  apply card_image_eq_of_fibers_iff
  intro A hA B hB
  simpa only [support_setPolynomial, Function.comp_apply] using
    differenceMultiset_eq_iff_autocorrelation_eq
      (setPolynomial_endpoints hA) (setPolynomial_endpoints hB)

/-- Exact finite upper and lower bounds, including degree one. Division by two
expresses the half-sized reflection orbits without truncated exponents. -/
theorem differenceMultisetFamily_card_bounds {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ^ (n - 1) / 2 * (1 - 8 * (3 / 4 : ℝ) ^ ((n - 1) / 4)) ≤
        ((differenceMultisetFamily n).card : ℝ) ∧
      ((differenceMultisetFamily n).card : ℝ) ≤
        (2 : ℝ) ^ (n - 1) / 2 + (2 : ℝ) ^ (n / 2) / 2 := by
  rw [card_differenceMultisetFamily hn]
  constructor
  · have h := binaryAutocorrelationFamily_card_lower (n - 1)
    rw [Nat.sub_add_cancel hn] at h
    have hp := mod_four_companion_probability_le n hn
    have hs : (2 : ℝ) ^ (n - 1) * (1 - 8 * (3 / 4 : ℝ) ^ ((n - 1) / 4)) ≤
        2 * ((binaryAutocorrelationFamily (n - 1)).card : ℝ) := by
      apply le_trans _ h
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left hp 1) (by positivity)
    nlinarith
  · have h := binaryAutocorrelationFamily_card_upper (n - 1)
    rw [Nat.sub_add_cancel hn] at h
    have hR : 2 * ((binaryAutocorrelationFamily (n - 1)).card : ℝ) ≤
        (2 : ℝ) ^ (n - 1) + (2 : ℝ) ^ (n / 2) := by exact_mod_cast h
    linarith

end OdlyzkoPoonen
