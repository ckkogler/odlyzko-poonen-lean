import OdlyzkoPoonen.Polynomial.MonicIrreducibleDivisor
import OdlyzkoPoonen.Polynomial.DivisorCount
import OdlyzkoPoonen.Polynomial.CyclotomicDivisors
import OdlyzkoPoonen.Probability.ReciprocalIntegerDivisors

/-!
# A small irreducible witness or a large reciprocal divisor

For a binary polynomial without a cyclotomic divisor, each nonconstant monic
reciprocal divisor either exceeds the chosen degree scale or contains an actual
noncyclotomic irreducible factor in the finite coefficient-bounded candidate pool.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma HasBinaryEndpoints.reciprocal_divisor_candidate_alternative {n L : ℕ} {P : ℤ[X]}
    (hP : HasBinaryEndpoints n P) (hrec : HasLargeReciprocalIntegerDivisor 1 P)
    (hcyc : ¬ HasCyclotomicDivisor P) :
    (∃ J ∈ smallDivisorCandidates L, Irreducible (J.map (Int.castRingHom ℚ)) ∧
      ¬ HasCyclotomicDivisor J ∧ J ∣ P) ∨ HasLargeReciprocalIntegerDivisor L P := by
  obtain ⟨D, hD, hDP, hDrec, hDpos⟩ := hrec
  by_cases hDL : D.natDegree ≤ L
  · obtain ⟨J, hJ, hirr, hJD⟩ := exists_monic_rational_irreducible_divisor hD hDpos
    have hJP : J ∣ P := hJD.trans hDP
    have hdeg : J.natDegree ≤ L := (natDegree_le_of_dvd hJD hD.ne_zero).trans hDL
    have hpos : 0 < J.natDegree := by
      have h := hirr.natDegree_pos
      rwa [hJ.natDegree_map] at h
    have hJcyc : ¬ HasCyclotomicDivisor J := by
      rintro ⟨k, hk, hdiv⟩
      exact hcyc ⟨k, hk, hdiv.trans hJP⟩
    exact Or.inl ⟨J, hP.monic_divisor_mem_candidates hJ hJP hpos hdeg, hirr, hJcyc, hJP⟩
  · exact Or.inr ⟨D, hD, hDP, hDrec, by omega⟩

end OdlyzkoPoonen
