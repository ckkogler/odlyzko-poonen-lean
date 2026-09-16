import OdlyzkoPoonen.LinearAlgebra.ConfluentVandermonde
import OdlyzkoPoonen.LinearAlgebra.DeterminantNormBound
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Coarse norm bounds for the confluent Vandermonde determinant

Each divided-derivative coefficient is bounded using `choose(j,r) <= n^r`.
The resulting determinant estimate retains the product of the node sizes,
which will become a Mahler measure after grouping conjugates.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma norm_confluentVandermonde_entry_le {n : ℕ} (x : Fin n → ℂ) (i j : Fin n) :
    ‖confluentVandermonde x i j‖ ≤
      (n : ℝ) ^ rootPrefixMultiplicity x i * (max 1 ‖x i‖) ^ n := by
  have hc : ((j.val.choose (rootPrefixMultiplicity x i) : ℕ) : ℝ) ≤
      (n : ℝ) ^ rootPrefixMultiplicity x i := by
    exact_mod_cast (Nat.choose_le_pow j.val (rootPrefixMultiplicity x i)).trans
      (Nat.pow_le_pow_left j.isLt.le _)
  have hm : ‖x i‖ ^ (j.val - rootPrefixMultiplicity x i) ≤ (max 1 ‖x i‖) ^ n := by
    calc
      _ ≤ (max 1 ‖x i‖) ^ (j.val - rootPrefixMultiplicity x i) :=
        pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
      _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) ((Nat.sub_le _ _).trans j.isLt.le)
  simp only [confluentVandermonde, norm_mul, Complex.norm_natCast, norm_pow]
  exact mul_le_mul hc hm (by positivity) (by positivity)

lemma norm_det_confluentVandermonde_le {n : ℕ} (x : Fin n → ℂ) :
    ‖(confluentVandermonde x).det‖ ≤
      (n.factorial : ℝ) * (n : ℝ) ^ (∑ i, rootPrefixMultiplicity x i) *
        (∏ i, max 1 ‖x i‖) ^ n := by
  have h := norm_det_le_factorial_mul_prod (confluentVandermonde x)
    (fun i ↦ (n : ℝ) ^ rootPrefixMultiplicity x i * (max 1 ‖x i‖) ^ n)
    (norm_confluentVandermonde_entry_le x)
  simpa only [Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow, mul_assoc] using h

lemma norm_det_confluentVandermonde_le_power {n : ℕ} (x : Fin n → ℂ) :
    ‖(confluentVandermonde x).det‖ ≤
      (n : ℝ) ^ (n + ∑ i, rootPrefixMultiplicity x i) * (∏ i, max 1 ‖x i‖) ^ n := by
  have hf : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc
    _ ≤ (n.factorial : ℝ) * (n : ℝ) ^ (∑ i, rootPrefixMultiplicity x i) *
        (∏ i, max 1 ‖x i‖) ^ n := norm_det_confluentVandermonde_le x
    _ ≤ (n : ℝ) ^ n * (n : ℝ) ^ (∑ i, rootPrefixMultiplicity x i) *
        (∏ i, max 1 ‖x i‖) ^ n := by gcongr
    _ = _ := by rw [pow_add]

end OdlyzkoPoonen
