import OdlyzkoPoonen.Analysis.UniformQuantitativeMahler
import OdlyzkoPoonen.Analysis.LogarithmicScale
import OdlyzkoPoonen.Analysis.SparseMahlerScale
import OdlyzkoPoonen.Polynomial.LogarithmicRootPowerPrime
import OdlyzkoPoonen.Probability.ReciprocalSumDivisors

/-!
# A uniform prime for determining residue-class coefficients

Every noncyclotomic irreducible monic factor of degree at most `n` has a
determining prime of size at most a fixed multiple of `(log n)^4`. All constants
and the degree threshold are chosen before the factor. The measure estimate
also covers the shifted contraction used for arbitrary residue classes.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma exists_uniform_residue_determining_prime :
    ∃ K : ℝ, 3 ≤ K ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      1 ≤ Real.log (n : ℝ) ∧ 64 * K * Real.log (n : ℝ) ^ 4 ≤ (n : ℝ) ∧
      ∀ J : ℤ[X], J.Monic → Irreducible (J.map (Int.castRingHom ℚ)) →
        J.coeff 0 ≠ 0 → (¬ HasCyclotomicDivisor J) → J.natDegree ≤ n →
        ∃ q : ℕ, q.Prime ∧ 3 ≤ q ∧ 4 * q ≤ n ∧
          K * Real.log (n : ℝ) ^ 4 < (q : ℝ) ∧
          (q : ℝ) ≤ 16 * K * Real.log (n : ℝ) ^ 4 ∧
          IsResidueDeterminingFactor (n - 1) q J := by
  obtain ⟨C, hC, hprime⟩ := exists_uniform_logarithmic_root_power_prime
  obtain ⟨c, hc, N₀, hN₀, hmahler⟩ := exists_uniform_quantitative_log_mahler_bound
  let K := max 3 (max (2 * C) (1 / c))
  have hK3 : 3 ≤ K := le_max_left _ _
  have hKC : 2 * C ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKc : 1 / c ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨N₁, hN₁, hscale⟩ := exists_threshold_logarithmic_prime_scale K
  refine ⟨K, hK3, max N₀ N₁, hN₀.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := (le_max_right _ _).trans hn
  have hn2 : 2 ≤ n := hN₁.trans hn₁
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hlog, hsmall⟩ := hscale n hn₁
  refine ⟨hlog, hsmall, ?_⟩
  intro J hJ hirr hconst hcyc hdeg
  have hd : 0 < J.natDegree := by
    have h := hirr.natDegree_pos
    rwa [hJ.natDegree_map] at h
  have hlogs : Real.log (J.natDegree : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdeg)
  have hthreshold : C * (1 + Real.log (J.natDegree : ℝ)) ≤ K * Real.log (n : ℝ) ^ 4 :=
    logarithmic_prime_scale_ge hC.le hKC hlog hlogs
  obtain ⟨q, hq, hqlo, hqhi, hsep⟩ :=
    hprime J hJ hirr hconst (K * Real.log (n : ℝ) ^ 4) hthreshold
  have hqhi' : (q : ℝ) ≤ 16 * K * Real.log (n : ℝ) ^ 4 := by nlinarith [hqhi]
  have hq3 : 3 ≤ q := by
    have hp : (1 : ℝ) ≤ Real.log (n : ℝ) ^ 4 := one_le_pow₀ hlog
    have : (3 : ℝ) < q := by nlinarith
    exact_mod_cast this.le
  have hqsmall : 4 * q ≤ n := by
    have : (4 : ℝ) * q ≤ n := by linarith
    exact_mod_cast this
  have hM : c / Real.log (n : ℝ) ^ 3 ≤
      Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure :=
    hmahler hJ hirr hconst hcyc n hn₀ hdeg
  have hnM : (n : ℝ) < (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ q := by
    apply (Real.lt_pow_iff_log_lt hn0 (mahlerMeasure_pos_of_ne_zero (hJ.map _).ne_zero)).mpr
    exact log_lt_prime_mul_log_of_mahler_gap hc hKc hlog hqlo hM
  have hroot : Real.sqrt (((n - 1 + q + 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hn0.le, ?_⟩
    have he : n - 1 + q + 1 = n + q := by omega
    rw [he, Nat.cast_add]
    have hqn : (q : ℝ) ≤ n := by exact_mod_cast (show q ≤ n by omega)
    nlinarith
  exact ⟨q, hq, hq3, hqsmall, hqlo, hqhi', hJ, hirr, hsep, hroot.trans_lt hnM⟩

end OdlyzkoPoonen
