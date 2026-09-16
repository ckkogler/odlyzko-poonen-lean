import Mathlib.Tactic

/-!
# The exact geometric factor in asymmetry averaging

Combining the first-asymmetry probability `2^(-j)` with a conditional weight
`(3/4)^(m-j)` leaves the geometric ratio `2/3`. Its positive-index sum is at most
`2`, uniformly in the finite upper cutoff.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma asymmetry_weight_factor {m j : ℕ} (hj : j ≤ m) :
    (1 / 2 : ℝ) ^ j * (3 / 4 : ℝ) ^ (m - j) =
      (3 / 4 : ℝ) ^ m * (2 / 3 : ℝ) ^ j := by
  have h : (1 / 2 : ℝ) = (3 / 4) * (2 / 3) := by norm_num
  rw [h, mul_pow, mul_right_comm, ← pow_add, show j + (m - j) = m by omega]

lemma sum_two_thirds_positive (s : ℕ) :
    (∑ i ∈ Finset.range s, (2 / 3 : ℝ) ^ (i + 1)) = 2 * (1 - (2 / 3 : ℝ) ^ s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

lemma sum_two_thirds_positive_le_two (s : ℕ) :
    (∑ i : Fin s, (2 / 3 : ℝ) ^ (i.val + 1)) ≤ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (2 / 3 : ℝ) ^ (i + 1)) s,
    sum_two_thirds_positive]
  have h : 0 ≤ (2 / 3 : ℝ) ^ s := by positivity
  linarith

lemma asymmetry_geometric_sum_le {s m : ℕ} (hs : s ≤ m) :
    (∑ i : Fin s, (1 / 2 : ℝ) ^ (i.val + 1) * (3 / 4 : ℝ) ^ (m - (i.val + 1))) ≤
      2 * (3 / 4 : ℝ) ^ m := by
  have hterm (i : Fin s) : i.val + 1 ≤ m := by have := i.isLt; omega
  simp_rw [asymmetry_weight_factor (hterm _)]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (3 / 4 : ℝ) ^ m * 2 := mul_le_mul_of_nonneg_left (sum_two_thirds_positive_le_two s) (by positivity)
    _ = _ := mul_comm _ _

end OdlyzkoPoonen
