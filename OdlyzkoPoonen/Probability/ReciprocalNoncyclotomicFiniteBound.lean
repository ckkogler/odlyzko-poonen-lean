import OdlyzkoPoonen.Polynomial.ReciprocalDivisorCandidates
import OdlyzkoPoonen.Probability.NoncyclotomicFactor
import OdlyzkoPoonen.Probability.FiniteSetUnion
import OdlyzkoPoonen.Probability.FiniteEvents

/-!
# The finite bound for noncyclotomic reciprocal divisors

The exact finite coefficient pool and the uniform fixed-factor estimate bound
small witnesses. The reciprocal gcd tail controls large witnesses. The bound
retains both terms and the constants four and six, for every natural cutoff.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped Classical

lemma exists_noncyclotomic_reciprocal_finite_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ L : ℕ,
      binaryProbability (n - 1) (fun P ↦
        HasLargeReciprocalIntegerDivisor 1 P ∧ ¬ HasCyclotomicDivisor P) ≤
        Real.exp (4 * (L : ℝ) ^ 2 - a * (n : ℝ) / Real.log (n : ℝ) ^ 4) +
          6 * (2 : ℝ) ^ (-(L : ℝ) / 2) := by
  obtain ⟨a, ha, N, hN, hfactor⟩ := exists_uniform_noncyclotomic_factor_bound
  refine ⟨a, ha, N, hN, ?_⟩
  intro n hn L
  let t := (smallDivisorCandidates L).filter (fun J ↦
    Irreducible (J.map (Int.castRingHom ℚ)) ∧ ¬ HasCyclotomicDivisor J)
  have hn1 : 1 ≤ n := by omega
  have hsub : binaryProbability (n - 1) (fun P ↦
      HasLargeReciprocalIntegerDivisor 1 P ∧ ¬ HasCyclotomicDivisor P) ≤
      binaryProbability (n - 1) (fun P ↦
        (∃ J ∈ t, J ∣ P) ∨ HasLargeReciprocalIntegerDivisor L P) := by
    apply uniformProbability_mono
    intro w hw
    rcases (wordPolynomial_endpoints w).reciprocal_divisor_candidate_alternative hw.1 hw.2 with h | h
    · obtain ⟨J, hmem, hirr, hcyc, hdiv⟩ := h
      exact Or.inl ⟨J, Finset.mem_filter.mpr ⟨hmem, hirr, hcyc⟩, hdiv⟩
    · exact Or.inr h
  have hsmall : binaryProbability (n - 1) (fun P ↦ ∃ J ∈ t, J ∣ P) ≤
      (t.card : ℝ) * Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
    apply uniformProbability_exists_mem_le_card_mul t
    intro J hJ
    obtain ⟨_, hirr, hcyc⟩ := Finset.mem_filter.mp hJ
    exact hfactor n hn J hirr hcyc
  have hcard : (t.card : ℝ) ≤ Real.exp (4 * (L : ℝ) ^ 2) := by
    have h : t.card ≤ (smallDivisorCandidates L).card := Finset.card_filter_le _ _
    exact (by exact_mod_cast h : (t.card : ℝ) ≤ (smallDivisorCandidates L).card).trans
      (card_smallDivisorCandidates_le_exp L)
  have hsmall' : binaryProbability (n - 1) (fun P ↦ ∃ J ∈ t, J ∣ P) ≤
      Real.exp (4 * (L : ℝ) ^ 2 - a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
    calc
      _ ≤ (t.card : ℝ) * Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := hsmall
      _ ≤ Real.exp (4 * (L : ℝ) ^ 2) *
          Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  exact hsub.trans ((binaryProbability_or_le_add _ _ _).trans
    (add_le_add hsmall' (binaryProbability_large_reciprocal_divisor_le hn1 L)))

end OdlyzkoPoonen
