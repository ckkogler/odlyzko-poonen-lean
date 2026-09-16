import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic

/-!
# Binary polynomials with fixed endpoints

The coefficient predicate refers to ordinary integer polynomials. The family
`HasBinaryEndpoints n` records precisely monicity, degree `n`, constant one and
zero-one coefficients; no irreducibility or probability information is built in.
-/

namespace OdlyzkoPoonen

open Polynomial

/-- Every coefficient of the integer polynomial is zero or one. -/
def IsBinary (p : ℤ[X]) : Prop := ∀ k, p.coeff k = 0 ∨ p.coeff k = 1

/-- The monic binary degree-`n` family with constant coefficient one. -/
structure HasBinaryEndpoints (n : ℕ) (p : ℤ[X]) : Prop where
  monic : p.Monic
  degree : p.natDegree = n
  constant : p.coeff 0 = 1
  binary : IsBinary p

lemma IsBinary.coeff_nonneg {p : ℤ[X]} (hp : IsBinary p) (k : ℕ) :
    0 ≤ p.coeff k := by
  rcases hp k with h | h <;> simp [h]

lemma IsBinary.coeff_le_one {p : ℤ[X]} (hp : IsBinary p) (k : ℕ) :
    p.coeff k ≤ 1 := by
  rcases hp k with h | h <;> simp [h]

lemma IsBinary.coeff_sq {p : ℤ[X]} (hp : IsBinary p) (k : ℕ) :
    p.coeff k ^ 2 = p.coeff k := by
  rcases hp k with h | h <;> simp [h]

lemma isBinary_iff_coeff_sq (p : ℤ[X]) :
    IsBinary p ↔ ∀ k, p.coeff k ^ 2 = p.coeff k := by
  constructor
  · exact fun hp ↦ hp.coeff_sq
  · intro hp k
    have h : p.coeff k * (p.coeff k - 1) = 0 := by nlinarith [hp k]
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)

lemma HasBinaryEndpoints.ne_zero {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : p ≠ 0 := hp.monic.ne_zero

lemma HasBinaryEndpoints.coeff_degree {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : p.coeff n = 1 := by
  rw [← hp.degree]
  exact hp.monic

lemma HasBinaryEndpoints.coeff_eq_zero_above {n k : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hk : n < k) : p.coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt (hp.degree ▸ hk)

lemma HasBinaryEndpoints.natTrailingDegree {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : p.natTrailingDegree = 0 := by
  exact Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (by rw [hp.constant]; norm_num))

end OdlyzkoPoonen
