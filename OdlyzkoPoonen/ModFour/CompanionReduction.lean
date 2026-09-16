import OdlyzkoPoonen.FiniteField.CompanionFactorization

/-!
# Reducing and parametrizing actual binary companions

A nontrivial companion is another binary endpoint polynomial of the same degree,
distinct from the original and its reverse, with autocorrelation congruent
modulo four. Reduction modulo two gives the finite-field parametrization.
Injectivity of reduction on binary polynomials preserves nontriviality, and
zero-one lifting recovers the original integer polynomials exactly.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma CongruentMod.of_dvd {r s : ℕ} {p q : ℤ[X]}
    (h : CongruentMod s p q) (hrs : r ∣ s) : CongruentMod r p q := by
  apply (congruentMod_iff_coeff_dvd r p q).mpr
  intro k
  have hcast : (r : ℤ) ∣ (s : ℤ) := by exact_mod_cast hrs
  exact hcast.trans ((congruentMod_iff_coeff_dvd s p q).mp h k)

/-- The precise nontrivial companion event on integer binary polynomials. -/
def HasModFourCompanion (n : ℕ) (p : ℤ[X]) : Prop :=
  ∃ q : ℤ[X], HasBinaryEndpoints n q ∧ q ≠ p ∧ q ≠ p.reverse ∧
    CongruentMod 4 (autocorrelation p) (autocorrelation q)

lemma binary_autocorrelations_reduce_eq {p q : ℤ[X]} (hp : IsBinary p) (hq : IsBinary q)
    (h : CongruentMod 4 (autocorrelation p) (autocorrelation q)) :
    reducePolynomial 2 p * (reducePolynomial 2 p).reverse =
      reducePolynomial 2 q * (reducePolynomial 2 q).reverse := by
  have h2 := h.of_dvd (by norm_num : 2 ∣ 4)
  change reducePolynomial 2 (p * p.reverse) = reducePolynomial 2 (q * q.reverse) at h2
  simpa only [reducePolynomial_mul, hp.reduce_reverse, hq.reduce_reverse] using h2

lemma HasModFourCompanion.factorization {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hcomp : HasModFourCompanion n p) :
    ∃ (d e : ℕ) (a b : (ZMod 2)[X]),
      1 ≤ d ∧ d ≤ e ∧ d + e = n ∧ HasF2Endpoints d a ∧ HasF2Endpoints e b ∧
      p = zeroOneLift (a * b) ∧ a ≠ a.reverse ∧
      CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
        (autocorrelation (zeroOneLift (a * b.reverse))) := by
  obtain ⟨q, hq, hne, hrev, hcong⟩ := hcomp
  have hn2 : reducePolynomial 2 q ≠ reducePolynomial 2 p := by
    intro h
    exact hne (hq.binary.eq_of_reduce_eq hp.binary h)
  have hr2 : reducePolynomial 2 q ≠ (reducePolynomial 2 p).reverse := by
    intro h
    apply hrev
    apply hq.binary.eq_of_reduce_eq hp.binary.reverse
    simpa only [hp.binary.reduce_reverse] using h
  obtain ⟨d, e, a, b, hd, hde, hdeg, ha, hb, hFab, hna, _, hGab⟩ :=
    ordered_companion_factorization hp.reduce hq.reduce
      (binary_autocorrelations_reduce_eq hp.binary hq.binary hcong) hn2 hr2
  have hpab : p = zeroOneLift (a * b) := by
    simpa only [zeroOneLift_reduce hp.binary] using congrArg zeroOneLift hFab
  refine ⟨d, e, a, b, hd, hde, hdeg, ha, hb, hpab, hna, ?_⟩
  rw [← hpab]
  rcases hGab with hGab | hGab
  · have hqab : q = zeroOneLift (a * b.reverse) := by
      simpa only [zeroOneLift_reduce hq.binary] using congrArg zeroOneLift hGab
    simpa only [← hqab] using hcong
  · have hqab : q.reverse = zeroOneLift (a * b.reverse) := by
      simpa only [zeroOneLift_reverse, zeroOneLift_reduce hq.binary] using
        congrArg zeroOneLift hGab
    rw [← hqab, autocorrelation_reverse (by rw [hq.constant]; exact one_ne_zero)]
    exact hcong

end OdlyzkoPoonen
