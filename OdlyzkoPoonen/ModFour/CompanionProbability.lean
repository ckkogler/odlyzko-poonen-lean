import OdlyzkoPoonen.ModFour.CompanionUnionBound
import OdlyzkoPoonen.ModFour.SplitGeometricBound

/-!
# Probability of a nontrivial modulo-four autocorrelation companion

For a uniformly chosen monic binary polynomial of degree `n ≥ 1` with constant
one, the probability of a distinct companion other than its reverse is bounded
by the degree-split sum, and that sum is at most `8*(3/4)^floor((n-1)/4)`.
Both inequalities use the actual finite polynomial family and the full
coefficientwise congruence modulo four.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma companion_split_sum_eq_Icc (n : ℕ) :
    (∑ i : Fin (n / 2), (3 / 4 : ℝ) ^ ((n - (i.val + 1) - 1) / 2)) =
      ∑ d ∈ Finset.Icc 1 (n / 2), (3 / 4 : ℝ) ^ ((n - d - 1) / 2) := by
  symm
  have hset : Finset.Icc 1 (n / 2) = Finset.Ico 1 (n / 2 + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range
    (fun d : ℕ ↦ (3 / 4 : ℝ) ^ ((n - d - 1) / 2)) 1 (n / 2 + 1), Nat.add_sub_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (3 / 4 : ℝ) ^ ((n - (i + 1) - 1) / 2)) (n / 2)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.add_comm 1 i]

/-- The two exact degree-split bounds for nontrivial autocorrelation companions. -/
theorem mod_four_companion_probability (n : ℕ) (hn : 1 ≤ n) :
    binaryProbability (n - 1) (HasModFourCompanion n) ≤
        (∑ d ∈ Finset.Icc 1 (n / 2), (3 / 4 : ℝ) ^ ((n - d - 1) / 2)) ∧
      (∑ d ∈ Finset.Icc 1 (n / 2), (3 / 4 : ℝ) ^ ((n - d - 1) / 2)) ≤
        8 * (3 / 4 : ℝ) ^ ((n - 1) / 4) := by
  rw [← companion_split_sum_eq_Icc]
  exact ⟨binaryProbability_companion_le_split_sum n hn, companion_split_sum_le_eight n⟩

lemma mod_four_companion_probability_le (n : ℕ) (hn : 1 ≤ n) :
    binaryProbability (n - 1) (HasModFourCompanion n) ≤
      8 * (3 / 4 : ℝ) ^ ((n - 1) / 4) :=
  (mod_four_companion_probability n hn).1.trans (mod_four_companion_probability n hn).2

end OdlyzkoPoonen
