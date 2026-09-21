import OdlyzkoPoonen.Polynomial.CyclotomicReciprocity
import OdlyzkoPoonen.Polynomial.CyclotomicProductDivisors
import OdlyzkoPoonen.Probability.NoncyclotomicReciprocalDivisor
import OdlyzkoPoonen.Reducibility.FactorAlternative

/-!
# Irreducibility after removing all cyclotomic factors

Outside the companion and noncyclotomic reciprocal-divisor events, the monic
remainder after removing cyclotomic factors is either one or irreducible.
A reciprocal degree cutoff excludes the unit remainder and bounds the entire
cyclotomic part, with multiplicity.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma HasBinaryEndpoints.cyclotomic_remainder_one_or_irreducible
    {n : ℕ} {P Q R : ℤ[X]} (hp : HasBinaryEndpoints n P)
    (hPR : P = Q * R) (hQ : IsCyclotomicProduct Q) (hR : R.Monic)
    (hcyc : ¬ HasCyclotomicDivisor R) (hcomp : ¬ HasModFourCompanion n P)
    (hbad : ¬ HasNoncyclotomicReciprocalDivisor P) : R = 1 ∨ Irreducible R := by
  by_cases hR1 : R = 1
  · exact Or.inl hR1
  right
  by_contra hred
  have hdeg : 0 < R.natDegree := by
    by_contra h
    exact hR1 (hR.natDegree_eq_zero.mp (by omega))
  obtain ⟨A, B, hA, hB, hAB, hAd, hBd⟩ :=
    monic_factors_of_reducibleOverRat hR hdeg ((monic_reducibleOverRat_iff hR).mpr hred)
  have hAR : A ∣ R := ⟨B, hAB⟩
  have hBR : B ∣ R := ⟨A, by rw [hAB, mul_comm]⟩
  have hRP : R ∣ P := ⟨Q, by rw [hPR, mul_comm]⟩
  have hAnot : ¬ IsCyclotomicProduct A :=
    not_isCyclotomicProduct_of_monic_nonconstant_noncyclotomic hA hAd
      (fun h ↦ hcyc (h.of_dvd hAR))
  have hBnot : ¬ IsCyclotomicProduct B :=
    not_isCyclotomicProduct_of_monic_nonconstant_noncyclotomic hB hBd
      (fun h ↦ hcyc (h.of_dvd hBR))
  have hArev : A ≠ A.reverse := fun h ↦ hbad ⟨A, hA, hAR.trans hRP, h.symm, hAnot⟩
  have hBrev : B ≠ B.reverse := fun h ↦ hbad ⟨B, hB, hBR.trans hRP, h.symm, hBnot⟩
  have hQrev : Q.reverse = Q := hp.cyclotomic_product_reciprocal hQ ⟨R, hPR⟩
  have hQBrev : Q * B ≠ (Q * B).reverse := by
    intro h
    rw [reverse_mul_of_domain, hQrev] at h
    exact hBrev (mul_left_cancel₀ hQ.monic.ne_zero h)
  have hPAB : P = A * (Q * B) := by rw [hPR, hAB]; ring
  obtain ⟨_, _, hnew, hcorr, heq, hrev⟩ := binary_factor_reversal hp hA (hQ.monic.mul hB) hPAB
  apply hcomp
  refine ⟨A * (Q * B).reverse, hnew, fun h ↦ hQBrev (heq.mp h),
    fun h ↦ hArev (hrev.mp h), ?_⟩
  exact congrArg (reducePolynomial 4) hcorr.symm

def HasIrreducibleNoncyclotomicPart (P : ℤ[X]) : Prop :=
  ∃ Q R : ℤ[X], P = Q * R ∧ IsCyclotomicProduct Q ∧
    Irreducible R ∧ ¬ HasCyclotomicDivisor R

def HasIrreducibleNoncyclotomicPartBelow (L : ℕ) (P : ℤ[X]) : Prop :=
  ∃ Q R : ℤ[X], P = Q * R ∧ IsCyclotomicProduct Q ∧
    Irreducible R ∧ ¬ HasCyclotomicDivisor R ∧ Q.natDegree < L

lemma HasIrreducibleNoncyclotomicPartBelow.forget {L : ℕ} {P : ℤ[X]}
    (h : HasIrreducibleNoncyclotomicPartBelow L P) : HasIrreducibleNoncyclotomicPart P := by
  obtain ⟨Q, R, hPR, hQ, hR, hcyc, _⟩ := h
  exact ⟨Q, R, hPR, hQ, hR, hcyc⟩

lemma HasBinaryEndpoints.irreducibleNoncyclotomicPartBelow {n L : ℕ} {P : ℤ[X]}
    (hp : HasBinaryEndpoints n P) (hL : L ≤ n)
    (hcomp : ¬ HasModFourCompanion n P) (hbad : ¬ HasNoncyclotomicReciprocalDivisor P)
    (htail : ¬ HasLargeReciprocalIntegerDivisor L P) :
    HasIrreducibleNoncyclotomicPartBelow L P := by
  obtain ⟨Q, R, hPR, hQ, hR, hcyc⟩ := exists_cyclotomic_factorization hp.monic
  have hQrec : Q.reverse = Q := hp.cyclotomic_product_reciprocal hQ ⟨R, hPR⟩
  have hQlt : Q.natDegree < L := by
    by_contra h
    exact htail ⟨Q, hQ.monic, ⟨R, hPR⟩, hQrec, by omega⟩
  have hRi := hp.cyclotomic_remainder_one_or_irreducible hPR hQ hR hcyc hcomp hbad
  rcases hRi with hR1 | hRi
  · have he : P = Q := by simpa [hR1] using hPR
    have hdegree : Q.natDegree = n := he ▸ hp.degree
    omega
  · exact ⟨Q, R, hPR, hQ, hRi, hcyc, hQlt⟩

end OdlyzkoPoonen
