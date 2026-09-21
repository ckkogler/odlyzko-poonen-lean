import OdlyzkoPoonen.Polynomial.CyclotomicFactorization
import OdlyzkoPoonen.Polynomial.ReciprocalDivisorReduction
import OdlyzkoPoonen.Polynomial.UniformResidueDeterminingPrime
import OdlyzkoPoonen.Probability.ReciprocalResidueBound
import OdlyzkoPoonen.Analysis.FiniteExponentialExtension

/-!
# Reciprocal divisors beyond cyclotomic products

A monic reciprocal divisor that is not a cyclotomic product contains a
noncyclotomic irreducible factor dividing both the sampled polynomial and its
integer reciprocal sum. Only finitely many primes are needed to separate the
candidate roots. Averaging the selected unequal pairs and taking the finite
union gives a uniform logarithmic exponential probability bound.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical

def HasNoncyclotomicReciprocalDivisor (P : ℤ[X]) : Prop :=
  ∃ H : ℤ[X], H.Monic ∧ H ∣ P ∧ H.reverse = H ∧ ¬ IsCyclotomicProduct H

lemma noncyclotomic_reciprocal_divisor_witness {P : ℤ[X]}
    (h : HasNoncyclotomicReciprocalDivisor P) :
    ∃ J : ℤ[X], J.Monic ∧ Irreducible (J.map (Int.castRingHom ℚ)) ∧
      ¬ HasCyclotomicDivisor J ∧ J ∣ P ∧ J ∣ P + P.reverse := by
  obtain ⟨H, hH, hHP, hrec, hnot⟩ := h
  obtain ⟨J, hJ, hirr, hcyc, hJH⟩ :=
    exists_noncyclotomic_irreducible_divisor_of_not_product hH hnot
  have hHr : H ∣ P.reverse := by
    obtain ⟨B, hB⟩ := hHP
    refine ⟨B.reverse, ?_⟩
    rw [hB, reverse_mul_of_domain, hrec]
  exact ⟨J, hJ, hirr, hcyc, hJH.trans hHP,
    dvd_add (hJH.trans hHP) (hJH.trans hHr)⟩

lemma exists_noncyclotomic_reciprocal_divisor_prefactor_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      binaryProbability (n - 1) HasNoncyclotomicReciprocalDivisor ≤
        (n : ℝ) ^ 2 * Real.exp (-a * n / Real.log (n : ℝ) ^ 4) := by
  obtain ⟨K, hK, N, hN, hprime⟩ := exists_uniform_residue_determining_prime
  have hK0 : 0 < K := by linarith
  refine ⟨1 / (256 * K), by positivity, N, hN, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := hN.trans hn
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hlog, hscale, hchoose⟩ := hprime n hn
  let B : ℝ := 16 * K * Real.log (n : ℝ) ^ 4
  let primes := (Finset.range n).filter (fun q ↦
    q.Prime ∧ 3 ≤ q ∧ 4 * q ≤ n ∧ (q : ℝ) ≤ B)
  have hbound : binaryProbability (n - 1) HasNoncyclotomicReciprocalDivisor ≤
      primes.card * ((n : ℝ) * Real.exp (-(n : ℝ) / (16 * B))) := by
    refine (uniformProbability_mono ?_).trans
      (uniformProbability_exists_mem_le_card_mul primes
        (fun q (w : Fin (n - 1) → Bool) ↦
          HasSeparatedReciprocalSumDivisor (n - 1) q (wordPolynomial w))
        ((n : ℝ) * Real.exp (-(n : ℝ) / (16 * B))) ?_)
    · intro w hw
      obtain ⟨J, hJ, hirr, hcyc, hd, hsum⟩ := noncyclotomic_reciprocal_divisor_witness hw
      have hp := wordPolynomial_endpoints w
      have hconst : J.coeff 0 ≠ 0 := by
        rw [hp.monic_divisor_constant hJ hd]
        norm_num
      have hdeg : J.natDegree ≤ n := by
        have h := natDegree_le_of_dvd hd hp.ne_zero
        rwa [hp.degree, Nat.sub_add_cancel hn1] at h
      obtain ⟨q, hq, hq3, hqn, hqlo, hqhi, hdet⟩ := hchoose J hJ hirr hconst hcyc hdeg
      refine ⟨q, ?_, J, hdet, hd, hsum⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq, hq3, hqn, hqhi⟩
    · intro q hq
      obtain ⟨_, hp, hq3, hqn, hqB⟩ := Finset.mem_filter.mp hq
      exact binaryProbability_reciprocalSumDivisor_le_exp hp hq3 hqn hqB
  calc
    _ ≤ primes.card * ((n : ℝ) * Real.exp (-(n : ℝ) / (16 * B))) := hbound
    _ ≤ (n : ℝ) * ((n : ℝ) * Real.exp (-(n : ℝ) / (16 * B))) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (Finset.card_filter_le (Finset.range n) _).trans_eq (Finset.card_range n)
      · positivity
    _ = _ := by
      dsimp [B]
      have he : -(n : ℝ) / (16 * (16 * K * Real.log (n : ℝ) ^ 4)) =
          -(1 / (256 * K)) * n / Real.log (n : ℝ) ^ 4 := by ring
      rw [he]
      ring

theorem noncyclotomic_reciprocal_divisor_probability :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 3 ≤ n →
      binaryProbability (n - 1) HasNoncyclotomicReciprocalDivisor ≤
        C * Real.exp (-c * n / Real.log (n : ℝ) ^ 4) := by
  obtain ⟨a, ha, N₀, _, hbound⟩ := exists_noncyclotomic_reciprocal_divisor_prefactor_bound
  obtain ⟨N₁, _, habsorb⟩ := exists_threshold_absorb_quadratic_logarithmic_exp ha
  have he : ∀ n : ℕ, max N₀ N₁ ≤ n →
      binaryProbability (n - 1) HasNoncyclotomicReciprocalDivisor ≤
        Real.exp (-(a / 2) * n / Real.log (n : ℝ) ^ 4) := by
    intro n hn
    exact (hbound n ((le_max_left _ _).trans hn)).trans
      (habsorb n ((le_max_right _ _).trans hn))
  obtain ⟨C, hC, hfinal⟩ := extend_logarithmic_exponential_bound
    (show 0 < a / 2 by positivity)
    (fun n ↦ uniformProbability_le_one (fun w : Fin (n - 1) → Bool ↦
      HasNoncyclotomicReciprocalDivisor (wordPolynomial w))) he
  exact ⟨a / 2, C, by positivity, hC, hfinal⟩

end OdlyzkoPoonen
