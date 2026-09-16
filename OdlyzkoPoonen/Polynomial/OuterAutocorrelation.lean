import OdlyzkoPoonen.Polynomial.Autocorrelation

/-!
# Outer autocorrelation coefficients

The coefficient at index `k` depends only on the first and last `k+1`
coefficients. For endpoint-one polynomials the endpoint terms are linear, and
all remaining products involve strictly earlier opposite coefficient pairs.
This is the coefficient formula used in the modulo-four exposure argument.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

lemma coeff_autocorrelation_le (p : ℤ[X]) {k : ℕ} (hk : k ≤ p.natDegree) :
    (autocorrelation p).coeff k =
      ∑ i ∈ Finset.range (k + 1), p.coeff i * p.coeff (p.natDegree - k + i) := by
  rw [autocorrelation, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j ↦ p.coeff i * p.reverse.coeff j)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ k := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le (by omega),
    show p.natDegree - (k - i) = p.natDegree - k + i by omega]

lemma HasBinaryEndpoints.coeff_autocorrelation_outer {n k : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hk0 : 0 < k) (hk : k ≤ n) :
    (autocorrelation p).coeff k = p.coeff k + p.coeff (n - k) +
      ∑ i ∈ Finset.Ico 1 k, p.coeff i * p.coeff (n - k + i) := by
  rw [coeff_autocorrelation_le p (by rw [hp.degree]; exact hk), hp.degree]
  have hs := Finset.sum_range_add_sum_Ico
    (fun i ↦ p.coeff i * p.coeff (n - k + i)) (show 1 ≤ k by omega)
  rw [Finset.sum_range_succ, ← hs]
  simp only [Finset.sum_range_one, Nat.add_zero, Nat.sub_add_cancel hk,
    hp.constant, hp.coeff_degree, one_mul, mul_one]
  ring

lemma HasBinaryEndpoints.autocorrelation_outer_difference {n k : ℕ} {p q : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hq : HasBinaryEndpoints n q)
    (hk0 : 0 < k) (hk : k ≤ n)
    (hleft : ∀ i < k, p.coeff i = q.coeff i)
    (hright : ∀ i < k, p.coeff (n - i) = q.coeff (n - i)) :
    (autocorrelation p).coeff k - (autocorrelation q).coeff k =
      p.coeff k + p.coeff (n - k) - q.coeff k - q.coeff (n - k) := by
  have hs : (∑ i ∈ Finset.Ico 1 k, p.coeff i * p.coeff (n - k + i)) =
      ∑ i ∈ Finset.Ico 1 k, q.coeff i * q.coeff (n - k + i) := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hi0, hik⟩ := Finset.mem_Ico.mp hi
    rw [hleft i hik, show n - k + i = n - (k - i) by omega,
      hright (k - i) (by omega)]
  rw [hp.coeff_autocorrelation_outer hk0 hk, hq.coeff_autocorrelation_outer hk0 hk, hs]
  ring

end OdlyzkoPoonen
