import OdlyzkoPoonen.Polynomial.MonicReduction
import OdlyzkoPoonen.Polynomial.FactorReversal
import OdlyzkoPoonen.FiniteField.ReciprocalGcd

/-!
# Reciprocal integer divisors descend to the finite-field gcd

A monic divisor of an endpoint-one binary integer polynomial has constant one,
by the proved factor-constant lemma. Its reduction retains its degree. If the
divisor is reciprocal, the reduction divides both the reduced polynomial and
its reverse, hence their actual gcd. No binarity of the divisor is assumed.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma HasBinaryEndpoints.monic_divisor_constant {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p) : J.coeff 0 = 1 := by
  obtain ⟨q, hq⟩ := hdvd
  have hqmonic : q.Monic := hJ.of_mul_monic_left (by rw [← hq]; exact hp.monic)
  exact (hp.factor_constants hJ hqmonic hq).1

lemma HasBinaryEndpoints.monic_divisor_reduce_endpoints {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p) :
    HasF2Endpoints J.natDegree (reducePolynomial 2 J) := by
  refine ⟨hJ.map _, monic_reduce_natDegree 2 hJ, ?_⟩
  rw [coeff_reducePolynomial, hp.monic_divisor_constant hJ hdvd, Int.cast_one]

lemma monic_reciprocal_reduce_dvd_gcd {p J : ℤ[X]}
    (hJ : J.Monic) (hdvd : J ∣ p) (hrec : J.reverse = J) :
    reducePolynomial 2 J ∣
      GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse := by
  have hl := reducePolynomial_dvd 2 hdvd
  have hr := f2_reverse_dvd_reverse hl
  rw [← monic_reduce_reverse 2 hJ, hrec] at hr
  exact dvd_gcd hl hr

lemma HasBinaryEndpoints.reciprocal_divisor_degree_le_gcd {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p) (hrec : J.reverse = J) :
    J.natDegree ≤
      (GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse).natDegree := by
  have h := natDegree_le_of_dvd (monic_reciprocal_reduce_dvd_gcd hJ hdvd hrec)
    hp.reduce.gcd_reverse_endpoints.monic.ne_zero
  simpa only [monic_reduce_natDegree 2 hJ] using h

/-- Every monic reciprocal integer divisor gives a reciprocal divisor of the
actual finite-field gcd, with its degree unchanged. -/
theorem monic_reciprocal_divisor_reduction {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p) (hrec : J.reverse = J) :
    HasF2Endpoints J.natDegree (reducePolynomial 2 J) ∧
      (reducePolynomial 2 J).natDegree = J.natDegree ∧
      (reducePolynomial 2 J).reverse = reducePolynomial 2 J ∧
      reducePolynomial 2 J ∣
        GCDMonoid.gcd (reducePolynomial 2 p) (reducePolynomial 2 p).reverse := by
  refine ⟨hp.monic_divisor_reduce_endpoints hJ hdvd, monic_reduce_natDegree 2 hJ,
    ?_, monic_reciprocal_reduce_dvd_gcd hJ hdvd hrec⟩
  rw [← monic_reduce_reverse 2 hJ, hrec]

end OdlyzkoPoonen
