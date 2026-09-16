import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-!
# Taylor coefficients of products of linear factors

The coefficient at the multiplicity of a root is the product of its differences
from the other roots. Lower Taylor coefficients vanish. These identities will
supply the triangular entries in the confluent Vandermonde determinant proof.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma taylor_X_sub_C_self {R : Type*} [CommRing R] (a : R) :
    taylor a (X - C a) = X := by simp

lemma taylor_coeff_pow_X_sub_C_mul {R : Type*} [CommRing R]
    (a : R) (r k : ℕ) (Q : R[X]) :
    (taylor a ((X - C a) ^ r * Q)).coeff k =
      if r ≤ k then (taylor a Q).coeff (k - r) else 0 := by
  rw [taylor_mul, taylor_pow, taylor_X_sub_C_self, coeff_X_pow_mul']

lemma hasseDeriv_eval_pow_X_sub_C_mul {R : Type*} [CommRing R]
    (a : R) (r : ℕ) (Q : R[X]) :
    (hasseDeriv r ((X - C a) ^ r * Q)).eval a = Q.eval a := by
  rw [← taylor_coeff, taylor_coeff_pow_X_sub_C_mul]
  simp

lemma hasseDeriv_eval_pow_X_sub_C_mul_of_lt {R : Type*} [CommRing R]
    (a : R) {r k : ℕ} (hkr : k < r) (Q : R[X]) :
    (hasseDeriv k ((X - C a) ^ r * Q)).eval a = 0 := by
  rw [← taylor_coeff, taylor_coeff_pow_X_sub_C_mul, ite_eq_right (not_le.mpr hkr)]

lemma prod_X_sub_C_factor_at {ι R : Type*} [CommRing R]
    (s : Finset ι) (x : ι → R) (a : R) :
    (∏ i ∈ s, (X - C (x i))) =
      (X - C a) ^ (s.filter (fun i ↦ x i = a)).card *
        ∏ i ∈ s.filter (fun i ↦ x i ≠ a), (X - C (x i)) := by
  conv_lhs => rw [← Finset.prod_filter_mul_prod_filter_not s (fun i ↦ x i = a)
    (fun i ↦ (X - C (x i) : R[X]))]
  congr 1
  calc
    _ = ∏ _i ∈ s.filter (fun i ↦ x i = a), (X - C a : R[X]) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by rw [Finset.prod_const]

lemma hasseDeriv_prod_X_sub_C_eval_multiplicity {ι R : Type*} [CommRing R]
    (s : Finset ι) (x : ι → R) (a : R) :
    (hasseDeriv (s.filter (fun i ↦ x i = a)).card
      (∏ i ∈ s, (X - C (x i)))).eval a =
      ∏ i ∈ s.filter (fun i ↦ x i ≠ a), (a - x i) := by
  rw [prod_X_sub_C_factor_at s x a, hasseDeriv_eval_pow_X_sub_C_mul]
  simp only [eval_prod, eval_sub, eval_X, eval_C]

lemma hasseDeriv_prod_X_sub_C_eval_eq_zero_of_lt {ι R : Type*} [CommRing R]
    (s : Finset ι) (x : ι → R) (a : R) {k : ℕ}
    (hk : k < (s.filter (fun i ↦ x i = a)).card) :
    (hasseDeriv k (∏ i ∈ s, (X - C (x i)))).eval a = 0 := by
  rw [prod_X_sub_C_factor_at s x a]
  exact hasseDeriv_eval_pow_X_sub_C_mul_of_lt a hk _

end OdlyzkoPoonen
