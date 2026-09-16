import OdlyzkoPoonen.Probability.NoncyclotomicMonicFactor
import OdlyzkoPoonen.Polynomial.MonicDivisorSign

/-!
# The uniform noncyclotomic fixed-factor estimate

Every factor that can divide a sample is monic up to sign, and changing this
sign preserves the divisibility event. Thus the monic estimate gives a single
absolute constant and threshold for all rationally irreducible integer factors.
Zero constant coefficients, excessive degrees and nonmonic factors are handled
by the proved empty-event and sign reductions, not extra final hypotheses.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma exists_uniform_noncyclotomic_factor_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ J : ℤ[X], Irreducible (J.map (Int.castRingHom ℚ)) →
        (¬ HasCyclotomicDivisor J) →
        binaryProbability (n - 1) (fun P ↦ J ∣ P) ≤
          Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
  obtain ⟨a, ha, N, hN, hbound⟩ := exists_uniform_noncyclotomic_monic_factor_bound
  refine ⟨a, ha, N, hN, ?_⟩
  intro n hn J hirr hcyc
  by_cases hex : ∃ w : Fin (n - 1) → Bool, J ∣ wordPolynomial w
  · obtain ⟨w, hw⟩ := hex
    rcases monic_or_neg_monic_of_dvd_monic (wordPolynomial_endpoints w).monic hw with hJ | hJ
    · exact hbound n hn J hJ hirr hcyc
    · have hirr' : Irreducible ((-J).map (Int.castRingHom ℚ)) := by
        simpa only [Polynomial.map_neg] using (Associated.refl (J.map (Int.castRingHom ℚ))).neg_right.irreducible hirr
      have hcyc' : ¬ HasCyclotomicDivisor (-J) := by
        rintro ⟨k, hk, hdiv⟩
        exact hcyc ⟨k, hk, dvd_neg.mp hdiv⟩
      simpa only [neg_dvd] using hbound n hn (-J) hJ hirr' hcyc'
  · have hf : ∀ w : Fin (n - 1) → Bool, ¬ J ∣ wordPolynomial w := by simpa using hex
    have hz : binaryProbability (n - 1) (fun P ↦ J ∣ P) = 0 := by
      simp [binaryProbability, uniformProbability, hf]
    rw [hz]
    exact (Real.exp_pos _).le

/-- The same absolute estimate with irreducibility in the integer polynomial ring. -/
lemma exists_uniform_integer_irreducible_noncyclotomic_factor_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ J : ℤ[X], Irreducible J → (¬ HasCyclotomicDivisor J) →
        binaryProbability (n - 1) (fun P ↦ J ∣ P) ≤
          Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
  obtain ⟨a, ha, N, hN, hbound⟩ := exists_uniform_noncyclotomic_factor_bound
  refine ⟨a, ha, N, hN, ?_⟩
  intro n hn J hirr hcyc
  by_cases hex : ∃ w : Fin (n - 1) → Bool, J ∣ wordPolynomial w
  · obtain ⟨w, hw⟩ := hex
    exact hbound n hn J
      (irreducible_map_rat_of_dvd_monic (wordPolynomial_endpoints w).monic hw hirr) hcyc
  · have hf : ∀ w : Fin (n - 1) → Bool, ¬ J ∣ wordPolynomial w := by simpa using hex
    have hz : binaryProbability (n - 1) (fun P ↦ J ∣ P) = 0 := by
      simp [binaryProbability, uniformProbability, hf]
    rw [hz]
    exact (Real.exp_pos _).le

end OdlyzkoPoonen
