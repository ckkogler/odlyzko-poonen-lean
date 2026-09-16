import OdlyzkoPoonen.Analysis.QuantitativeMahlerLargeDegree
import OdlyzkoPoonen.Analysis.BoundedDegreeMahlerGap

/-!
# A uniform quantitative noncyclotomic Mahler gap

The large-degree determinant bound and the finite bounded-degree gap give one
absolute positive constant. The denominator may use any sufficiently large
ambient degree bound, uniformly over all monic rationally irreducible integer
polynomials with nonzero constant term and no cyclotomic divisor.
-/

namespace OdlyzkoPoonen
open Polynomial Filter
open scoped Topology

lemma exists_uniform_quantitative_log_mahler_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ {J : ℤ[X]}, J.Monic →
      Irreducible (J.map (Int.castRingHom ℚ)) → J.coeff 0 ≠ 0 →
      (¬ HasCyclotomicDivisor J) → ∀ n : ℕ, N ≤ n → J.natDegree ≤ n →
        c / Real.log (n : ℝ) ^ 3 ≤ Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨D, hD, hlarge⟩ := exists_threshold_quantitative_mahler_large_degree
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_noncyclotomic_log_mahler_gap_bounded_degree D
  have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 1)
  refine ⟨min (1 / 18576) ε, lt_min (by norm_num) hε, max 2 N, le_max_left _ _, ?_⟩
  intro J hJ hirr hconst hcyc n hn hdn
  have hlogn : 1 ≤ Real.log (n : ℝ) := hN n ((le_max_right _ _).trans hn)
  have hlogn0 : 0 < Real.log (n : ℝ) := by linarith
  have hd : 0 < J.natDegree := by
    have h := hirr.natDegree_pos
    rwa [hJ.natDegree_map] at h
  by_cases hbig : D ≤ J.natDegree
  · have hd2 : 2 ≤ J.natDegree := hD.trans hbig
    have hlogd : 0 < Real.log (J.natDegree : ℝ) := Real.log_pos (by exact_mod_cast hd2)
    have hlogs : Real.log (J.natDegree : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by exact_mod_cast hd) (by exact_mod_cast hdn)
    calc
      min (1 / 18576) ε / Real.log (n : ℝ) ^ 3 ≤
          (1 / 18576) / Real.log (n : ℝ) ^ 3 :=
        div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      _ ≤ (1 / 18576) / Real.log (J.natDegree : ℝ) ^ 3 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (pow_le_pow_left₀ hlogd.le hlogs 3)
      _ = 1 / (18576 * Real.log (J.natDegree : ℝ) ^ 3) := by rw [div_div]
      _ ≤ _ := hlarge hJ hirr hconst hcyc hbig
  · have hX : ¬ X ∣ J := fun h ↦ hconst (X_dvd_iff.mp h)
    have hgap := hsmall J hd (by omega) hX hcyc
    apply le_trans _ hgap
    apply (div_le_iff₀ (pow_pos hlogn0 3)).mpr
    exact (min_le_right _ _).trans
      (le_mul_of_one_le_right hε.le (one_le_pow₀ hlogn))

end OdlyzkoPoonen
