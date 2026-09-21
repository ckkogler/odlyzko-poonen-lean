import OdlyzkoPoonen.Polynomial.Autocorrelation
import OdlyzkoPoonen.Polynomial.BinaryWords
import Mathlib.Data.Multiset.Filter

/-!
# Signed difference multisets

The multiset records one signed difference for each ordered pair of elements,
including repetitions and the zero differences. For a binary polynomial its
multiplicities are exactly the coefficients of the reciprocal product, shifted
by the degree.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

/-- All ordered signed differences of a finite set, with their multiplicities. -/
def differenceMultiset (A : Finset ℕ) : Multiset ℤ :=
  (A.product A).val.map (fun ab ↦ (ab.1 : ℤ) - (ab.2 : ℤ))

lemma count_differenceMultiset (A : Finset ℕ) (z : ℤ) :
    (differenceMultiset A).count z =
      ((A.product A).filter (fun ab ↦ z = (ab.1 : ℤ) - (ab.2 : ℤ))).card := by
  simp only [differenceMultiset, Multiset.count_map, ← Finset.filter_val,
    Finset.card_def]

lemma IsBinary.eq_sum_support_X_pow {p : ℤ[X]} (hp : IsBinary p) :
    p = ∑ i ∈ p.support, X ^ i := by
  conv_lhs => rw [← p.sum_C_mul_X_pow_eq, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro i hi
  have hc : p.coeff i = 1 := (hp i).resolve_left (mem_support_iff.mp hi)
  simp [hc]

lemma HasBinaryEndpoints.reverse_eq_sum {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) :
    p.reverse = ∑ j ∈ p.support, X ^ (n - j) := by
  let F : ℤ[X] →+ ℤ[X] :=
    { toFun := Polynomial.reflect n
      map_zero' := Polynomial.reflect_zero
      map_add' := fun p q ↦ Polynomial.reflect_add p q n }
  have h := congrArg F hp.binary.eq_sum_support_X_pow
  rw [map_sum] at h
  change Polynomial.reflect n p = _ at h
  rw [Polynomial.reverse, hp.degree]
  refine h.trans (Finset.sum_congr rfl ?_)
  intro j hj
  have hjn : j ≤ n := hp.degree ▸ le_natDegree_of_mem_supp j hj
  change Polynomial.reflect n (X ^ j : ℤ[X]) = _
  rw [Polynomial.reflect_monomial, Polynomial.revAt_le hjn]

lemma HasBinaryEndpoints.autocorrelation_eq_sum {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) :
    autocorrelation p = ∑ ab ∈ p.support.product p.support,
      X ^ (ab.1 + (n - ab.2)) := by
  unfold autocorrelation
  rw [hp.reverse_eq_sum]
  conv_lhs => lhs; rw [hp.binary.eq_sum_support_X_pow]
  rw [Finset.sum_mul_sum]
  calc
    _ = ∑ i ∈ p.support, ∑ j ∈ p.support, (X : ℤ[X]) ^ (i + (n - j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [← pow_add]
    _ = _ := (Finset.sum_product p.support p.support
      (fun ab : ℕ × ℕ ↦ (X : ℤ[X]) ^ (ab.1 + (n - ab.2)))).symm

lemma HasBinaryEndpoints.coeff_autocorrelation_eq_count {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (k : ℕ) :
    (autocorrelation p).coeff k =
      ((differenceMultiset p.support).count ((k : ℤ) - (n : ℤ)) : ℤ) := by
  rw [hp.autocorrelation_eq_sum, finsetSum_coeff, count_differenceMultiset]
  simp only [Polynomial.coeff_X_pow, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ab hab
  have hj : ab.2 ≤ n := hp.degree ▸
    le_natDegree_of_mem_supp ab.2 (Finset.mem_product.mp hab).2
  have he : ab.1 + (n - ab.2) = k ↔
      (k : ℤ) - (n : ℤ) = (ab.1 : ℤ) - (ab.2 : ℤ) := by omega
  by_cases h : ab.1 + (n - ab.2) = k
  · simp [h, he.mp h]
  · have hz : ¬ (k : ℤ) - (n : ℤ) = (ab.1 : ℤ) - (ab.2 : ℤ) :=
      fun H ↦ h (he.mpr H)
    simp [Ne.symm h, hz]

lemma HasBinaryEndpoints.difference_count_eq_zero {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) {z : ℤ} (hz : z < -(n : ℤ)) :
    (differenceMultiset p.support).count z = 0 := by
  rw [count_differenceMultiset]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ab hab
  obtain ⟨hab, he⟩ := Finset.mem_filter.mp hab
  have hj : ab.2 ≤ n := hp.degree ▸
    le_natDegree_of_mem_supp ab.2 (Finset.mem_product.mp hab).2
  omega

/-- Equality of signed difference multisets is exactly equality of reciprocal
products for endpoint-fixed binary polynomials of the same degree. -/
theorem differenceMultiset_eq_iff_autocorrelation_eq {n : ℕ} {p q : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hq : HasBinaryEndpoints n q) :
    differenceMultiset p.support = differenceMultiset q.support ↔
      autocorrelation p = autocorrelation q := by
  constructor
  · intro h
    ext k
    rw [hp.coeff_autocorrelation_eq_count, hq.coeff_autocorrelation_eq_count, h]
  · intro h
    apply Multiset.ext.mpr
    intro z
    by_cases hz : z < -(n : ℤ)
    · rw [hp.difference_count_eq_zero hz, hq.difference_count_eq_zero hz]
    · let k := (z + (n : ℤ)).toNat
      have hk : (k : ℤ) - (n : ℤ) = z := by
        dsimp [k]
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      have he := congrArg (fun P : ℤ[X] ↦ P.coeff k) h
      rw [hp.coeff_autocorrelation_eq_count, hq.coeff_autocorrelation_eq_count, hk] at he
      exact_mod_cast he

end OdlyzkoPoonen
