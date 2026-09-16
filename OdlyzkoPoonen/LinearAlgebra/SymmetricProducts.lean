import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic

/-!
# Products of symmetric pair factors

The full product of a symmetric array with diagonal one is the square of its
strict lower-triangular product. This form is convenient for reindexing a
confluent determinant by groups of repeated roots.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma prod_symmetric_eq_lower_sq {ι M : Type*} [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [CommMonoid M] (f : ι → ι → M) (hsym : ∀ i j, f i j = f j i)
    (hdiag : ∀ i, f i i = 1) :
    (∏ i, ∏ j, f i j) = (∏ i, ∏ j ∈ Finset.Iio i, f i j) ^ 2 := by
  classical
  have hf (i j : ι) : f i j =
      (if j < i then f i j else 1) * (if i < j then f i j else 1) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [hdiag]
    · simp [h, not_lt_of_gt h]
  have he : (∏ i, ∏ j, if i < j then f i j else 1) =
      ∏ i, ∏ j, if j < i then f i j else 1 := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    rw [hsym j i]
  calc
    (∏ i, ∏ j, f i j) = ∏ i, ∏ j,
        ((if j < i then f i j else 1) * (if i < j then f i j else 1)) := by
      exact Finset.prod_congr rfl (fun i _ ↦ Finset.prod_congr rfl (fun j _ ↦ hf i j))
    _ = (∏ i, ∏ j, if j < i then f i j else 1) *
        (∏ i, ∏ j, if i < j then f i j else 1) := by
      simp only [Finset.prod_mul_distrib]
    _ = (∏ i, ∏ j, if j < i then f i j else 1) ^ 2 := by rw [he, pow_two]
    _ = _ := by
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      simp only [← Finset.prod_filter]
      congr 1
      ext j
      simp

end OdlyzkoPoonen
