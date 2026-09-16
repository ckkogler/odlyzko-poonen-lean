import OdlyzkoPoonen.Polynomial.Reversal

/-!
# The central autocorrelation coefficient and binary rigidity

The central coefficient is the sum of the coefficient squares. For an integer
polynomial, equality of that sum with the coefficient sum forces every
coefficient to be zero or one: each integer `z * (z - 1)` is nonnegative.
This is the arithmetic reason that factor reversal preserves binarity.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

lemma coeff_autocorrelation_middle (p : ℤ[X]) :
    (autocorrelation p).coeff p.natDegree =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i ^ 2 := by
  rw [autocorrelation, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ p.coeff i * p.reverse.coeff j)]
  apply Finset.sum_congr rfl
  intro i hi
  have h : i ≤ p.natDegree := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le (Nat.sub_le _ _),
    Nat.sub_sub_self h, pow_two]

lemma eval_one_eq_sum_coeff (p : ℤ[X]) :
    p.eval 1 = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := by
  simp [Polynomial.eval_eq_sum_range]

lemma int_mul_sub_one_nonneg (z : ℤ) : 0 ≤ z * (z - 1) := by
  by_cases hz : z ≤ 0
  · exact mul_nonneg_of_nonpos_of_nonpos hz (by omega)
  · exact mul_nonneg (by omega) (by omega)

lemma isBinary_of_sum_sq_eq_sum (q : ℤ[X])
    (hq : (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i ^ 2) =
      ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i) : IsBinary q := by
  have hz : (∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * (q.coeff i - 1)) = 0 := by
    simp_rw [mul_sub, mul_one, ← pow_two]
    rw [Finset.sum_sub_distrib, hq, sub_self]
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.range (q.natDegree + 1)) ↦
      int_mul_sub_one_nonneg (q.coeff i))).mp hz
  intro k
  by_cases hk : k ≤ q.natDegree
  · rcases mul_eq_zero.mp (hall k (Finset.mem_range.mpr (by omega))) with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · exact Or.inl (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))

/-- Equal autocorrelations and equal coefficient sums force binarity at the
same degree. The degree hypothesis will be derived for factor reversal. -/
lemma IsBinary.of_autocorrelation_eq {p q : ℤ[X]} (hp : IsBinary p)
    (hdegree : q.natDegree = p.natDegree)
    (hc : autocorrelation q = autocorrelation p) (he : q.eval 1 = p.eval 1) :
    IsBinary q := by
  apply isBinary_of_sum_sq_eq_sum
  calc
    (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i ^ 2) =
        (autocorrelation q).coeff q.natDegree := (coeff_autocorrelation_middle q).symm
    _ = (autocorrelation p).coeff p.natDegree := by rw [hc, hdegree]
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i ^ 2 :=
      coeff_autocorrelation_middle p
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := by
      apply Finset.sum_congr rfl
      intro i _
      exact hp.coeff_sq i
    _ = p.eval 1 := (eval_one_eq_sum_coeff p).symm
    _ = q.eval 1 := he.symm
    _ = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i := eval_one_eq_sum_coeff q

end OdlyzkoPoonen
