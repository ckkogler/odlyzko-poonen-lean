import OdlyzkoPoonen.FiniteField.FirstAsymmetry
import OdlyzkoPoonen.Probability.AverageBounds

/-!
# Exact law of the first asymmetric pair

The first nonzero coefficient of `p+p.reverse` is an event of the original
uniform endpoint-one polynomial. The actual opposite-pair coordinate bijection
identifies it with the first true pair-sum bit. Averaging out the lower word
and optional center gives probability exactly `2^(-j)`, without conditioning
on nonreciprocity.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma f2Probability_firstAsymmetryAt {n : ℕ} (i : Fin (n / 2)) :
    f2Probability n (fun p ↦ FirstAsymmetryAt p (i.val + 1)) =
      (1 / 2 : ℝ) ^ (i.val + 1) := by
  rw [f2Probability_eq_paired_average]
  simp only [firstAsymmetryAt_paired_iff]
  simp_rw [uniformProbability_eq_average_indicator, uniformAverage_const]
  rw [← uniformProbability_eq_average_indicator, uniformProbability_firstTrueAt]

lemma HasF2Endpoints.exists_firstAsymmetry_range {d : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints d p) (hd : 0 < d) (hne : p ≠ p.reverse) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ (d - 1) / 2 ∧ FirstAsymmetryAt p j := by
  cases d with
  | zero => omega
  | succ n =>
    obtain ⟨i, hi⟩ := hp.exists_firstAsymmetry hne
    exact ⟨i.val + 1, by omega, by have := i.isLt; omega, hi⟩

/-- The source's positive, one-based index and exponent, for arbitrary degree. -/
lemma f2Probability_firstAsymmetryAt_of_range {n j : ℕ}
    (hj0 : 1 ≤ j) (hj : j ≤ n / 2) :
    f2Probability n (fun p ↦ FirstAsymmetryAt p j) = (1 / 2 : ℝ) ^ j := by
  let i : Fin (n / 2) := ⟨j - 1, by omega⟩
  have hi : i.val + 1 = j := by dsimp [i]; omega
  simpa only [hi] using f2Probability_firstAsymmetryAt i

/-- Degrees one and two have no asymmetric pairs. -/
lemma HasF2Endpoints.reverse_eq_of_degree_le_two {d : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints d p) (hd0 : 0 < d) (hd : d ≤ 2) : p.reverse = p := by
  by_contra h
  obtain ⟨j, hj0, hj, _⟩ := hp.exists_firstAsymmetry_range hd0 (Ne.symm h)
  omega

end OdlyzkoPoonen
