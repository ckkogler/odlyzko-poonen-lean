import OdlyzkoPoonen.Probability.ReciprocalIntegerDivisors
import OdlyzkoPoonen.Polynomial.MonicDivisorSign
import OdlyzkoPoonen.Polynomial.CyclotomicDivisors

/-!
# Removing a sign convention from reciprocal divisors

Every integer divisor of a monic polynomial is monic up to sign. Negation
preserves divisibility, degree and reciprocity, so requiring a monic witness
does not restrict the existence event. This explicitly connects the normalized
finite-counting argument to arbitrary nonconstant reciprocal integer divisors.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma hasLargeReciprocalIntegerDivisor_iff {P : ℤ[X]} (hP : P.Monic) (L : ℕ) :
    HasLargeReciprocalIntegerDivisor L P ↔
      ∃ J : ℤ[X], J ∣ P ∧ J.reverse = J ∧ L ≤ J.natDegree := by
  constructor
  · rintro ⟨J, _, hdiv, hrec, hL⟩
    exact ⟨J, hdiv, hrec, hL⟩
  · rintro ⟨J, hdiv, hrec, hL⟩
    rcases monic_or_neg_monic_of_dvd_monic hP hdiv with hJ | hJ
    · exact ⟨J, hJ, hdiv, hrec, hL⟩
    · refine ⟨-J, hJ, neg_dvd.mpr hdiv, ?_, ?_⟩
      · simpa only [Polynomial.reverse_neg] using congrArg Neg.neg hrec
      · simpa only [Polynomial.natDegree_neg] using hL

lemma binaryProbability_reciprocal_noncyclotomic_unrestricted (m L : ℕ) :
    binaryProbability m (fun P ↦
      (∃ J : ℤ[X], J ∣ P ∧ J.reverse = J ∧ L ≤ J.natDegree) ∧
        ¬ HasCyclotomicDivisor P) =
      binaryProbability m (fun P ↦
        HasLargeReciprocalIntegerDivisor L P ∧ ¬ HasCyclotomicDivisor P) := by
  unfold binaryProbability
  congr 1
  funext w
  exact propext (and_congr_left fun _ ↦
    (hasLargeReciprocalIntegerDivisor_iff (wordPolynomial_endpoints w).monic L).symm)

end OdlyzkoPoonen
