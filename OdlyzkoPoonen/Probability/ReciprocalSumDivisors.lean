import OdlyzkoPoonen.Probability.AdaptiveFiniteConditioning
import OdlyzkoPoonen.Probability.SelectedBitWeights
import OdlyzkoPoonen.Polynomial.PairedWordSum
import OdlyzkoPoonen.Polynomial.IrreducibleDivisorFamily
import OdlyzkoPoonen.Polynomial.ResidueDivisorUniqueness
import OdlyzkoPoonen.Probability.BinaryModel

/-!
# Divisors selected by the integer reciprocal sum

The reciprocal sum selects at most `m+1` irreducible candidates. A separated
candidate of sufficiently large Mahler measure permits at most one assignment
on each selected set of unequal opposite pairs. Averaging over the pair mask
gives the exact factor `(3/4)^k`, with no exceptional conditioning event.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical

def IsResidueDeterminingFactor (m q : ℕ) (J : ℤ[X]) : Prop :=
  J.Monic ∧ Irreducible (J.map (Int.castRingHom ℚ)) ∧
    (∀ z ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ w ∈ (J.map (Int.castRingHom ℂ)).roots, z ^ q = w ^ q → z = w) ∧
    Real.sqrt ((m + q + 1 : ℕ) : ℝ) < (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ q

def HasSeparatedReciprocalSumDivisor (m q : ℕ) (P : ℤ[X]) : Prop :=
  ∃ J : ℤ[X], IsResidueDeterminingFactor m q J ∧ J ∣ P ∧ J ∣ P + P.reverse

lemma uniformProbability_reciprocalSumDivisor_conditioned_le {m q a : ℕ}
    (hq : 0 < q) (ha : a < q) (s : Finset (Fin (m / 2)))
    (hs : ∀ j ∈ s, ((lowerWordIndex j).val + 1) % q = a ∧
      ((upperWordIndex j).val + 1) % q = a)
    (c : Fin (m / 2) → Bool) (z : Fin (m % 2) → Bool) :
    uniformProbability (fun u : Fin (m / 2) → Bool ↦
      HasSeparatedReciprocalSumDivisor m q (wordPolynomial (assembleOppositeWord u c z))) ≤
      (m + 1) * (1 / 2 : ℝ) ^ selectedTrueCount s c := by
  let selected : Fin (m / 2) → Prop := fun j ↦ j ∈ s ∧ c j = true
  let statistic : (Fin (m / 2) → Bool) → {S : ℤ[X] // S.natDegree ≤ m + 1} :=
    fun u ↦ ⟨wordReciprocalSum (assembleOppositeWord u c z),
      (wordReciprocalSum_natDegree _).le⟩
  let family : {S : ℤ[X] // S.natDegree ≤ m + 1} → Finset ℤ[X] :=
    fun S ↦ monicIrreducibleDivisorFamily S.val
  let E : ℤ[X] → (Fin (m / 2) → Bool) → Prop := fun J u ↦
    IsResidueDeterminingFactor m q J ∧ J ∣ wordPolynomial (assembleOppositeWord u c z)
  have hbound := uniformProbability_adaptive_selected_le selected statistic family E (m + 1)
    (fun S ↦ (monicIrreducibleDivisorFamily_card_le S.val).trans S.property)
    (by
      intro u v hfixed
      apply Subtype.ext
      apply wordReciprocalSum_assemble_eq
      intro j hj
      apply hfixed
      simp [selected, hj])
    (by
      intro J u v hu hv hfixed
      have he := word_eq_of_rational_irreducible_residue_divisibility hq ha
        hu.1.1 hu.1.2.1 hu.1.2.2.1 hu.1.2.2.2
        (assembleOppositeWord u c z) (assembleOppositeWord v c z) hu.2 hv.2
        (assembleOppositeWord_agree_outside u v c z selected
          (fun i ↦ (i.val + 1) % q = a)
          (fun j hj ↦ hs j hj.1) hfixed)
      funext j
      have hh := congrFun he (lowerWordIndex j)
      simpa only [assembleOppositeWord_lower] using hh)
  have hcard : Fintype.card {j : Fin (m / 2) // selected j} = selectedTrueCount s c := by
    simp only [Fintype.card_subtype, selected, selectedTrueCount]
    congr 1
    ext j
    simp
  have hbound' : uniformProbability (fun u ↦ ∃ J ∈ family (statistic u), E J u) ≤
      (m + 1) * (1 / 2 : ℝ) ^ selectedTrueCount s c := by
    convert hbound using 1
    congr 2
    · simp
    · convert hcard.symm using 1
      congr 1
      exact Subsingleton.elim _ _
  refine (uniformProbability_mono ?_).trans hbound'
  intro u hu
  obtain ⟨J, hJ, hd, hsum⟩ := hu
  refine ⟨J, ?_, hJ, hd⟩
  exact (mem_monicIrreducibleDivisorFamily (wordReciprocalSum_ne_zero _)).mpr
    ⟨hJ.1, hJ.2.1, hsum⟩

lemma binaryProbability_reciprocalSumDivisor_le {m q a : ℕ}
    (hq : 0 < q) (ha : a < q) (s : Finset (Fin (m / 2)))
    (hs : ∀ j ∈ s, ((lowerWordIndex j).val + 1) % q = a ∧
      ((upperWordIndex j).val + 1) % q = a) :
    binaryProbability m (HasSeparatedReciprocalSumDivisor m q) ≤
      (m + 1) * (3 / 4 : ℝ) ^ s.card := by
  rw [binaryProbability, uniformProbability_oppositeWord]
  calc
    _ ≤ uniformAverage (fun c : Fin (m / 2) → Bool ↦
        (m + 1) * (1 / 2 : ℝ) ^ selectedTrueCount s c) := by
      apply uniformAverage_mono
      intro c
      apply uniformAverage_le
      intro z
      exact uniformProbability_reciprocalSumDivisor_conditioned_le hq ha s hs c z
    _ = _ := by
      simp_rw [mul_comm (m + 1 : ℝ)]
      rw [uniformAverage_mul_right]
      congr 1
      convert uniformAverage_selectedTrueHalfWeight s using 1
      congr 1
      exact Subsingleton.elim _ _

end OdlyzkoPoonen
