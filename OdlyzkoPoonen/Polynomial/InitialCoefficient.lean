import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-!
# Multiplication after the first nonzero coefficient

Vanishing below degree `j` factors a polynomial by `X^j`. If its coefficient
at `j` is one, the remaining factor has constant coefficient one. Multiplying
by a polynomial with zero constant then gives zero coefficients through `j`;
after the shift, each product coefficient is the corresponding input coefficient
plus a sum of earlier ones. These algebraic facts underlie triangular exposure.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

lemma exists_X_pow_factor_of_initial_one {R : Type*} [Semiring R]
    {p : R[X]} {j : ℕ} (hprev : ∀ k < j, p.coeff k = 0) (hj : p.coeff j = 1) :
    ∃ q : R[X], p = X ^ j * q ∧ q.coeff 0 = 1 := by
  obtain ⟨q, hq⟩ := X_pow_dvd_iff.mpr hprev
  refine ⟨q, hq, ?_⟩
  have h := coeff_X_pow_mul q j 0
  rw [zero_add, ← hq, hj] at h
  exact h.symm

lemma coeff_mul_zero_through_initial {R : Type*} [Semiring R]
    {p c : R[X]} {j k : ℕ} (hprev : ∀ i < j, p.coeff i = 0)
    (hc : c.coeff 0 = 0) (hk : k ≤ j) : (p * c).coeff k = 0 := by
  obtain ⟨q, hq⟩ := X_pow_dvd_iff.mpr hprev
  rw [hq, mul_assoc, coeff_X_pow_mul']
  by_cases hjk : j ≤ k
  · have heq : k = j := by omega
    simp only [heq, Nat.sub_self, mul_coeff_zero, hc, mul_zero, ite_self]
  · exact ite_eq_right hjk

lemma coeff_mul_after_X_pow_factor {R : Type*} [Semiring R]
    {p q : R[X]} (c : R[X]) {j : ℕ} (h : p = X ^ j * q) (r : ℕ) :
    (p * c).coeff (j + r) = (q * c).coeff r := by
  rw [h, mul_assoc, Nat.add_comm j r, coeff_X_pow_mul]

lemma coeff_mul_constant_one {R : Type*} [CommSemiring R]
    (q c : R[X]) (hq : q.coeff 0 = 1) (k : ℕ) :
    (q * c).coeff k = c.coeff k + ∑ i ∈ Finset.range k, c.coeff i * q.coeff (k - i) := by
  rw [mul_comm q c, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ c.coeff i * q.coeff j),
    Finset.sum_range_succ]
  simp only [Nat.sub_self, hq, mul_one]
  exact add_comm _ _

end OdlyzkoPoonen
