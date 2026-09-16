import OdlyzkoPoonen.Analysis.MahlerParameterBudget
import OdlyzkoPoonen.Analysis.MahlerParameterEstimates
import OdlyzkoPoonen.Analysis.RootPowerMahlerInequality
import OdlyzkoPoonen.Arithmetic.GoodRootPowerPrimes
import OdlyzkoPoonen.Analysis.IntegerMahlerMeasure

/-!
# An absolute logarithmic Mahler bound in large degree

Choose the multiplicity and prime interval by ceilings of `log d` and
`(log d)² log(log d)`. The actual separating prime family has enough logarithmic
weight, and its size and sum fit the proved determinant budget. The threshold
is absolute: it is chosen before the polynomial.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial Filter
open scoped BigOperators Classical Topology

lemma quantitative_mahler_of_large_log_degree {N : ℕ}
    (hweight : ∀ {J : ℤ[X]}, J.Monic →
      Irreducible (J.map (Int.castRingHom ℚ)) → J.coeff 0 ≠ 0 →
      ∀ n : ℕ, N ≤ n → Real.log (2 * (J.natDegree : ℝ) ^ 4) ≤ (n : ℝ) / 2 →
        (n : ℝ) / 2 ≤ ∑ p ∈ goodRootPowerPrimes J n (8 * n), Real.log (p : ℝ))
    {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J)
    (hL : 1 ≤ Real.log (J.natDegree : ℝ))
    (hlog : 3040 ≤ Real.log (Real.log (J.natDegree : ℝ)))
    (hNL : (N : ℝ) ≤ Real.log (J.natDegree : ℝ)) :
    1 / (18576 * Real.log (J.natDegree : ℝ) ^ 3) ≤
      Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  let L := Real.log (J.natDegree : ℝ)
  let k : ℕ := ⌈L⌉₊
  let n : ℕ := ⌈L ^ 2 * Real.log L⌉₊
  let t := goodRootPowerPrimes J n (8 * n)
  obtain ⟨hklo, hkup, hnlo, hnup, hLn, hn1⟩ := mahler_parameter_ceil_bounds hL hlog
  have hk : 0 < k := by
    have : (0 : ℝ) < (k : ℝ) := by dsimp [k, L]; linarith
    exact_mod_cast this
  have hnN : N ≤ n := by
    have : (N : ℝ) ≤ (n : ℝ) := hNL.trans hLn
    exact_mod_cast this
  have hn : 1 < n := by exact_mod_cast hn1
  have hd : 0 < J.natDegree := by
    have h := hirr.natDegree_pos
    rwa [hJ.natDegree_map] at h
  have hdreal : 0 < (J.natDegree : ℝ) := by exact_mod_cast hd
  have hbad : Real.log (2 * (J.natDegree : ℝ) ^ 4) ≤ (n : ℝ) / 2 :=
    mahler_bad_prime_log_budget hdreal rfl hL hlog hnlo
  have hw : (n : ℝ) / 2 ≤ ∑ p ∈ t, Real.log (p : ℝ) :=
    hweight hJ hirr hconst n hnN hbad
  have hlog1 : 1 ≤ Real.log L := by dsimp [L]; linarith
  have hs : (t.card : ℝ) ≤ 16 * L ^ 2 :=
    mahler_prime_card_budget hL hlog1 hnlo hnup (card_goodRootPowerPrimes_le J hn)
  have hsum : (∑ p ∈ t, (p : ℝ)) ≤ (t.card : ℝ) * (8 * (n : ℝ)) := by
    have h : ((∑ p ∈ t, p : ℕ) : ℝ) ≤ ((t.card * (8 * n) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (sum_goodRootPowerPrimes_le J n)
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using h
  have hS : (∑ p ∈ t, (p : ℝ)) ≤ 256 * L ^ 4 * Real.log L :=
    mahler_prime_sum_budget hL hlog1 hnup (Nat.cast_nonneg _) hs hsum
  have hd1 : (1 : ℝ) ≤ J.natDegree := by exact_mod_cast hd
  obtain ⟨hB, hBup⟩ := mahler_node_log_budget hd1 rfl hL hklo hkup (Nat.cast_nonneg _) hs
  have hp : ∀ p : t, (p : ℕ).Prime :=
    fun p ↦ (mem_goodRootPowerPrimes.mp p.property).1
  have hsep : ∀ p : t, ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ (p : ℕ) = b ^ (p : ℕ) → a = b :=
    fun p ↦ (mem_goodRootPowerPrimes.mp p.property).2.2.2
  have hmain := prime_family_mahler_log_inequality hJ hirr hconst hcyc
    (fun p : t ↦ (p : ℕ)) Subtype.val_injective hp hsep hk
  have hwcoe : (∑ p : t, Real.log ((p : ℕ) : ℝ)) = ∑ p ∈ t, Real.log (p : ℝ) := by
    exact Finset.sum_coe_sort t (fun p : ℕ ↦ Real.log (p : ℝ))
  rw [hwcoe] at hmain
  simp only [Fintype.card_coe, Finset.sum_coe_sort] at hmain
  have hlower : (k : ℝ) * (n : ℝ) / 2 ≤ (k : ℝ) * ∑ p ∈ t, Real.log (p : ℝ) := by
    have := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  exact mahler_log_lower_of_parameter_budget hL hlog hklo hkup hnlo
    (Nat.cast_nonneg _) hs hS hB hBup
    (Real.log_nonneg (one_le_mahlerMeasure_of_ne_zero hJ.ne_zero)) (hlower.trans hmain)

lemma exists_threshold_quantitative_mahler_large_degree :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {J : ℤ[X]}, J.Monic →
      Irreducible (J.map (Int.castRingHom ℚ)) → J.coeff 0 ≠ 0 →
      (¬ HasCyclotomicDivisor J) → D ≤ J.natDegree →
        1 / (18576 * Real.log (J.natDegree : ℝ) ^ 3) ≤
          Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨N, _hN, hw⟩ := exists_threshold_good_root_power_prime_weight
  have ht : Tendsto (fun d : ℕ ↦ Real.log (d : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htt : Tendsto (fun d : ℕ ↦ Real.log (Real.log (d : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp ht
  have he : ∀ᶠ d : ℕ in atTop, 2 ≤ d ∧ 1 ≤ Real.log (d : ℝ) ∧
      3040 ≤ Real.log (Real.log (d : ℝ)) ∧ (N : ℝ) ≤ Real.log (d : ℝ) := by
    filter_upwards [eventually_ge_atTop 2, ht.eventually_ge_atTop 1,
      htt.eventually_ge_atTop 3040, ht.eventually_ge_atTop (N : ℝ)] with d hd hl hll hn
    exact ⟨hd, hl, hll, hn⟩
  obtain ⟨D, hD⟩ := eventually_atTop.mp he
  refine ⟨max 2 D, le_max_left _ _, ?_⟩
  intro J hJ hirr hconst hcyc hdeg
  obtain ⟨_, hl, hll, hn⟩ := hD J.natDegree ((le_max_right _ _).trans hdeg)
  exact quantitative_mahler_of_large_log_degree hw hJ hirr hconst hcyc hl hll hn

end OdlyzkoPoonen
