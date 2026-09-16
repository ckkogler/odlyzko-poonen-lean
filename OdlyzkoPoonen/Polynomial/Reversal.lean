import OdlyzkoPoonen.Polynomial.Binary

/-!
# Reciprocal polynomials and exact reversal identities

Reversal is Mathlib's ordinary degree-based polynomial reversal. A nonzero
constant ensures that reversal preserves degree and is an involution.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma reverse_natDegree_of_constant_ne_zero {R : Type*} [Semiring R]
    {p : R[X]} (h : p.coeff 0 ≠ 0) : p.reverse.natDegree = p.natDegree := by
  rw [Polynomial.reverse_natDegree,
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr h), Nat.sub_zero]

lemma reverse_reverse_of_constant_ne_zero {R : Type*} [Semiring R]
    {p : R[X]} (h : p.coeff 0 ≠ 0) : p.reverse.reverse = p := by
  unfold Polynomial.reverse
  rw [show (p.reflect p.natDegree).natDegree = p.natDegree from
    reverse_natDegree_of_constant_ne_zero h]
  exact Polynomial.reflect_reflect

lemma IsBinary.reverse {p : ℤ[X]} (hp : IsBinary p) : IsBinary p.reverse := by
  intro k
  rw [Polynomial.coeff_reverse]
  exact hp _

lemma HasBinaryEndpoints.reverse {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : HasBinaryEndpoints n p.reverse := by
  have hc : p.coeff 0 ≠ 0 := by rw [hp.constant]; norm_num
  refine ⟨?_, ?_, ?_, hp.binary.reverse⟩
  · change p.reverse.leadingCoeff = 1
    rw [Polynomial.reverse_leadingCoeff, Polynomial.trailingCoeff_eq_coeff_zero hc,
      hp.constant]
  · rw [reverse_natDegree_of_constant_ne_zero hc, hp.degree]
  · rw [Polynomial.coeff_zero_reverse]
    exact hp.monic

lemma HasBinaryEndpoints.reverse_reverse {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : p.reverse.reverse = p :=
  reverse_reverse_of_constant_ne_zero (by rw [hp.constant]; norm_num)

/-- The aperiodic autocorrelation, as an ordinary integer polynomial. -/
noncomputable def autocorrelation (p : ℤ[X]) : ℤ[X] := p * p.reverse

lemma autocorrelation_reverse {p : ℤ[X]} (hp : p.coeff 0 ≠ 0) :
    autocorrelation p.reverse = autocorrelation p := by
  simp only [autocorrelation, reverse_reverse_of_constant_ne_zero hp, mul_comm]

lemma autocorrelation_mul (a b : ℤ[X]) :
    autocorrelation (a * b) = autocorrelation a * autocorrelation b := by
  simp only [autocorrelation, Polynomial.reverse_mul_of_domain]
  ring

lemma autocorrelation_factor_reverse (a : ℤ[X]) {b : ℤ[X]} (hb : b.coeff 0 ≠ 0) :
    autocorrelation (a * b.reverse) = autocorrelation (a * b) := by
  rw [autocorrelation_mul, autocorrelation_reverse hb, autocorrelation_mul]

end OdlyzkoPoonen
