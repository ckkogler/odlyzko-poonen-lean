import OdlyzkoPoonen.Polynomial.Autocorrelation

/-!
# Monic factor reversal of a binary polynomial

The coefficient-square identity proves binarity before either factor constant
is assigned a sign. The constant of the reversed product is then zero or one;
its nonvanishing forces both original factor constants to be one. This gives
an entirely algebraic proof of the factor-reversal lemma.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma eval_one_reverse (p : ℤ[X]) : p.reverse.eval 1 = p.eval 1 := by
  letI : Invertible (1 : ℤ) := invertibleOne
  have h := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℤ) (1 : ℤ) p
  simpa using h

lemma IsBinary.factor_reverse {p a b : ℤ[X]} (hp : IsBinary p)
    (h0 : p.coeff 0 ≠ 0) (ha : a.Monic) (hb : b.Monic) (hab : p = a * b) :
    IsBinary (a * b.reverse) := by
  have hb0 : b.coeff 0 ≠ 0 := by
    rw [hab, Polynomial.mul_coeff_zero] at h0
    exact (mul_ne_zero_iff.mp h0).2
  have hbr : b.reverse ≠ 0 := by simpa using hb.ne_zero
  apply hp.of_autocorrelation_eq
  · rw [Polynomial.natDegree_mul ha.ne_zero hbr,
      reverse_natDegree_of_constant_ne_zero hb0, hab,
      Polynomial.natDegree_mul ha.ne_zero hb.ne_zero]
  · rw [autocorrelation_factor_reverse a hb0, hab]
  · rw [Polynomial.eval_mul, eval_one_reverse, hab, Polynomial.eval_mul]

lemma HasBinaryEndpoints.factor_constants {n : ℕ} {p a b : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (ha : a.Monic) (hb : b.Monic) (hab : p = a * b) :
    a.coeff 0 = 1 ∧ b.coeff 0 = 1 := by
  have h0 : p.coeff 0 ≠ 0 := by rw [hp.constant]; norm_num
  have hq := hp.binary.factor_reverse h0 ha hb hab
  have hc : a.coeff 0 * b.coeff 0 = 1 := by
    rw [← Polynomial.mul_coeff_zero, ← hab, hp.constant]
  have ha0 : a.coeff 0 = 1 := by
    have h := hq 0
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_zero_reverse, hb.leadingCoeff,
      mul_one] at h
    rcases h with h | h
    · rw [h, zero_mul] at hc
      norm_num at hc
    · exact h
  exact ⟨ha0, by simpa [ha0] using hc⟩

lemma HasBinaryEndpoints.factor_reverse {n : ℕ} {p a b : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (ha : a.Monic) (hb : b.Monic) (hab : p = a * b) :
    HasBinaryEndpoints n (a * b.reverse) := by
  obtain ⟨ha0, hb0⟩ := hp.factor_constants ha hb hab
  have hbc : b.coeff 0 ≠ 0 := by rw [hb0]; norm_num
  have hbr : b.reverse ≠ 0 := by simpa using hb.ne_zero
  have hbmonic : b.reverse.Monic := by
    change b.reverse.leadingCoeff = 1
    rw [Polynomial.reverse_leadingCoeff, Polynomial.trailingCoeff_eq_coeff_zero hbc, hb0]
  refine ⟨ha.mul hbmonic, ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_mul ha.ne_zero hbr,
      reverse_natDegree_of_constant_ne_zero hbc,
      ← Polynomial.natDegree_mul ha.ne_zero hb.ne_zero, ← hab, hp.degree]
  · rw [Polynomial.mul_coeff_zero, Polynomial.coeff_zero_reverse, hb.leadingCoeff,
      ha0, mul_one]
  · exact hp.binary.factor_reverse (by rw [hp.constant]; norm_num) ha hb hab

lemma factor_reverse_eq_iff {a b : ℤ[X]} (ha : a ≠ 0) :
    a * b.reverse = a * b ↔ b = b.reverse := by
  constructor
  · intro h
    exact (mul_left_cancel₀ ha h).symm
  · intro h
    exact congrArg (fun q ↦ a * q) h.symm

lemma factor_reverse_eq_reverse_iff {a b : ℤ[X]} (hb : b ≠ 0) :
    a * b.reverse = (a * b).reverse ↔ a = a.reverse := by
  rw [Polynomial.reverse_mul_of_domain]
  have hbr : b.reverse ≠ 0 := by simpa using hb
  constructor
  · intro h
    exact mul_right_cancel₀ hbr h
  · intro h
    exact congrArg (fun q ↦ q * b.reverse) h

/-- Complete monic integer factor-reversal statement, with both triviality
criteria and the exact endpoint family. -/
theorem binary_factor_reversal {n : ℕ} {p a b : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (ha : a.Monic) (hb : b.Monic) (hab : p = a * b) :
    a.coeff 0 = 1 ∧ b.coeff 0 = 1 ∧ HasBinaryEndpoints n (a * b.reverse) ∧
      autocorrelation (a * b.reverse) = autocorrelation p ∧
      (a * b.reverse = p ↔ b = b.reverse) ∧
      (a * b.reverse = p.reverse ↔ a = a.reverse) := by
  obtain ⟨ha0, hb0⟩ := hp.factor_constants ha hb hab
  refine ⟨ha0, hb0, hp.factor_reverse ha hb hab, ?_, ?_, ?_⟩
  · rw [autocorrelation_factor_reverse a (by rw [hb0]; norm_num), hab]
  · rw [hab]
    exact factor_reverse_eq_iff ha.ne_zero
  · rw [hab]
    exact factor_reverse_eq_reverse_iff hb.ne_zero

end OdlyzkoPoonen
