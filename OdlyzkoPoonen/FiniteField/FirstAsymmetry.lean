import OdlyzkoPoonen.FiniteField.ReciprocalPairs
import OdlyzkoPoonen.FiniteField.BitTests
import OdlyzkoPoonen.Probability.FirstTrueBit

/-!
# The first asymmetric coefficient pair

The first asymmetry is defined by the actual first nonzero coefficient of
`p+p.reverse`. In opposite-pair coordinates, its positive index is precisely
one more than the first true bit of the pair-sum word. Every nonreciprocal
endpoint-one polynomial has such an index in the lower half.
-/

namespace OdlyzkoPoonen
open Polynomial

/-- The asymmetry polynomial has its first nonzero coefficient at `j`. -/
def FirstAsymmetryAt (p : (ZMod 2)[X]) (j : ℕ) : Prop :=
  (p + p.reverse).coeff j = 1 ∧ ∀ k < j, (p + p.reverse).coeff k = 0

lemma firstAsymmetryAt_paired_iff {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) (i : Fin (n / 2)) :
    FirstAsymmetryAt (pairedPolynomial u c z) (i.val + 1) ↔ FirstTrueAt c i := by
  constructor
  · rintro ⟨hi, hprev⟩
    rw [coeff_paired_sum_reverse_lower, bitToF2_eq_one_iff] at hi
    refine ⟨hi, ?_⟩
    intro j hj
    apply (bitToF2_eq_zero_iff _).mp
    rw [← coeff_paired_sum_reverse_lower u c z j]
    exact hprev (j.val + 1) (by have : j.val < i.val := hj; omega)
  · rintro ⟨hi, hprev⟩
    refine ⟨?_, ?_⟩
    · rw [coeff_paired_sum_reverse_lower, bitToF2_eq_one_iff]
      exact hi
    · intro k hk
      by_cases hk0 : k = 0
      · rw [hk0, coeff_add, (pairedPolynomial_endpoints u c z).constant,
          (pairedPolynomial_endpoints u c z).reverse.constant]
        exact CharTwo.add_self_eq_zero _
      · let j : Fin (n / 2) := ⟨k - 1, by have := i.isLt; omega⟩
        have hj : j.val + 1 = k := by dsimp [j]; omega
        rw [← hj, coeff_paired_sum_reverse_lower, bitToF2_eq_zero_iff]
        apply hprev j
        change j.val < i.val
        dsimp [j]
        omega

lemma FirstAsymmetryAt.unique {p : (ZMod 2)[X]} {i j : ℕ}
    (hi : FirstAsymmetryAt p i) (hj : FirstAsymmetryAt p j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hf := hj.2 i h
    rw [hi.1] at hf
    exact (one_ne_zero hf).elim
  · exact h
  · have hf := hi.2 j h
    rw [hj.1] at hf
    exact (one_ne_zero hf).elim

lemma FirstAsymmetryAt.ne_reverse {p : (ZMod 2)[X]} {j : ℕ}
    (h : FirstAsymmetryAt p j) : p ≠ p.reverse := by
  intro hp
  have hi := h.1
  rw [← hp, CharTwo.add_self_eq_zero, coeff_zero] at hi
  exact zero_ne_one hi

lemma HasF2Endpoints.exists_firstAsymmetry {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints (n + 1) p) (hne : p ≠ p.reverse) :
    ∃ i : Fin (n / 2), FirstAsymmetryAt p (i.val + 1) := by
  obtain ⟨w, rfl⟩ := exists_f2WordPolynomial_eq hp
  let v := oppositeWordEquiv n w
  have hw : pairedPolynomial v.2.2 v.1 v.2.1 = f2WordPolynomial w := by
    change f2WordPolynomial ((oppositeWordEquiv n).symm (oppositeWordEquiv n w)) = _
    rw [Equiv.symm_apply_apply]
  have hc : ¬ ∀ i, v.1 i = false := by
    intro hc
    have hr := (pairedPolynomial_reverse_eq_iff v.2.2 v.1 v.2.1).mpr hc
    rw [hw] at hr
    exact hne hr.symm
  obtain ⟨i, hi⟩ := (exists_firstTrueAt_iff v.1).mpr hc
  refine ⟨i, ?_⟩
  rw [← hw]
  exact (firstAsymmetryAt_paired_iff v.2.2 v.1 v.2.1 i).mpr hi

end OdlyzkoPoonen
