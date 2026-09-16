import OdlyzkoPoonen.Analysis.UniformQuantitativeMahler
import OdlyzkoPoonen.Analysis.LogarithmicScale
import OdlyzkoPoonen.Analysis.SparseMahlerScale
import OdlyzkoPoonen.Arithmetic.SparseQuotientBounds
import OdlyzkoPoonen.Polynomial.LogarithmicRootPowerPrime
import OdlyzkoPoonen.Probability.SparseDivisorBound
import OdlyzkoPoonen.Probability.IntegerDivisibility

/-!
# Uniform noncyclotomic monic fixed-factor probabilities

All separation and Mahler hypotheses of sparse uniqueness are discharged here.
The constants are selected before the polynomial or ambient degree. Impossible
constant coefficients and degrees give empty events, so no support assumptions
remain in this fixed-factor estimate.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma exists_uniform_noncyclotomic_monic_factor_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ J : ℤ[X], J.Monic → Irreducible (J.map (Int.castRingHom ℚ)) →
        (¬ HasCyclotomicDivisor J) →
        binaryProbability (n - 1) (fun P ↦ J ∣ P) ≤
          Real.exp (-a * (n : ℝ) / Real.log (n : ℝ) ^ 4) := by
  obtain ⟨C, hC, hprime⟩ := exists_uniform_logarithmic_root_power_prime
  obtain ⟨c, hc, N₀, hN₀, hmahler⟩ := exists_uniform_quantitative_log_mahler_bound
  let K := max (2 * C) (1 / c)
  have hK : 0 < K := (by positivity : 0 < 2 * C).trans_le (le_max_left _ _)
  have hKC : 2 * C ≤ K := le_max_left _ _
  have hKc : 1 / c ≤ K := le_max_right _ _
  obtain ⟨N₁, hN₁, hscale⟩ := exists_threshold_logarithmic_prime_scale K
  refine ⟨Real.log 2 / (64 * K), div_pos (Real.log_pos (by norm_num)) (by positivity),
    max N₀ N₁, hN₀.trans (le_max_left _ _), ?_⟩
  intro n hn J hJ hirr hcyc
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := (le_max_right _ _).trans hn
  have hn2 : 2 ≤ n := hN₁.trans hn₁
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < n := by linarith
  by_cases hconst : J.coeff 0 = 1
  swap
  · rw [binaryProbability_divisible_eq_zero_of_constant _ hJ hconst]
    exact (Real.exp_pos _).le
  by_cases hdeg : J.natDegree ≤ n
  swap
  · rw [binaryProbability_divisible_eq_zero_of_degree (by omega : 1 ≤ n) (by omega : n < J.natDegree)]
    exact (Real.exp_pos _).le
  have hconst0 : J.coeff 0 ≠ 0 := by rw [hconst]; norm_num
  obtain ⟨hlog, hsmall⟩ := hscale n hn₁
  have hd : 0 < J.natDegree := by
    have h := hirr.natDegree_pos
    rwa [hJ.natDegree_map] at h
  have hlogs : Real.log (J.natDegree : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdeg)
  have hthreshold : C * (1 + Real.log (J.natDegree : ℝ)) ≤ K * Real.log (n : ℝ) ^ 4 :=
    logarithmic_prime_scale_ge hC.le hKC hlog hlogs
  obtain ⟨q, hq, hqlo, hqhi, hsep⟩ :=
    hprime J hJ hirr hconst0 (K * Real.log (n : ℝ) ^ 4) hthreshold
  have hqhi' : (q : ℝ) ≤ 16 * K * Real.log (n : ℝ) ^ 4 := by nlinarith [hqhi]
  have hqm : q ≤ n - 1 := by
    have h : (q : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      linarith
    exact_mod_cast h
  have hM : c / Real.log (n : ℝ) ^ 3 ≤
      Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure :=
    hmahler hJ hirr hconst0 hcyc n hn₀ hdeg
  have hnM : (n : ℝ) < (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ q := by
    apply (Real.lt_pow_iff_log_lt hn0 (mahlerMeasure_pos_of_ne_zero (hJ.map _).ne_zero)).mpr
    exact log_lt_prime_mul_log_of_mahler_gap hc hKc hlog hqlo hM
  have hroot : Real.sqrt ((((n - 1) / q : ℕ) : ℝ)) ≤ (n : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hn0.le, ?_⟩
    have hfloor : ((((n - 1) / q : ℕ) : ℝ)) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.div_le_self (n - 1) q).trans (Nat.sub_le n 1)
    nlinarith
  exact (binaryProbability_rational_irreducible_divisible_le_sparse hq.pos hJ hirr
    hsep (hroot.trans_lt hnM)).trans (half_pow_sparse_quotient_le_exp hn2 hq.pos hqm hK hlog hqhi')

end OdlyzkoPoonen
