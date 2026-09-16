import OdlyzkoPoonen.Asymptotics.ReducibleNoncyclotomic
import OdlyzkoPoonen.Asymptotics.HigherCyclotomic
import OdlyzkoPoonen.Asymptotics.MinusOneAsymptotic
import OdlyzkoPoonen.Probability.EventComplement

/-!
# The sharp reducibility asymptotics

The noncyclotomic contribution is superpolynomially small and the higher
cyclotomic contribution is O(1/n). The remaining minus-one root event gives
both asymptotic formulas in Theorem 1.1, with its sharp leading constant.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped Topology

lemma binaryProbability_reducible_excess_isBigO :
    (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (fun P ↦ P.eval (-1) = 0)) =O[atTop]
        (fun n : ℕ ↦ 1 / (n : ℝ)) := by
  have hnoncyc : (fun n : ℕ ↦ binaryProbability (n - 1) (fun P ↦
      ReducibleOverRat P ∧ ¬ HasCyclotomicDivisor P)) =O[atTop]
        (fun n : ℕ ↦ 1 / (n : ℝ)) := by
    simpa only [Real.rpow_neg_one, one_div] using
      binaryProbability_reducible_noncyclotomic_isBigO 1 zero_lt_one
  have h := hnoncyc.add binaryProbability_higher_cyclotomic_isBigO
  refine (Asymptotics.IsBigO.of_norm_eventuallyLE ?_).trans h
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hsum : 0 ≤ binaryProbability (n - 1) (fun P ↦
      ReducibleOverRat P ∧ ¬ HasCyclotomicDivisor P) +
        binaryProbability (n - 1) HasHigherCyclotomicDivisor :=
    add_nonneg (uniformProbability_nonneg _) (uniformProbability_nonneg _)
  simpa only [Pi.add_apply, Real.norm_eq_abs,
    abs_of_nonneg (reducible_sub_minus_one_probability_nonneg hn), abs_of_nonneg hsum]
    using reducible_sub_minus_one_probability_le hn

/-- One positive constant controls the nonnegative excess for every large degree. -/
theorem exists_reducible_probability_excess_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      0 ≤ binaryProbability (n - 1) ReducibleOverRat -
        binaryProbability (n - 1) (fun P ↦ P.eval (-1) = 0) ∧
      binaryProbability (n - 1) ReducibleOverRat -
        binaryProbability (n - 1) (fun P ↦ P.eval (-1) = 0) ≤ C / (n : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := binaryProbability_reducible_excess_isBigO.exists_pos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound.bound
  refine ⟨C, hC, max 2 N, le_max_left _ _, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnonneg := reducible_sub_minus_one_probability_nonneg hn2
  refine ⟨hnonneg, ?_⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg (show (0 : ℝ) ≤ 1 / (n : ℝ) by positivity), mul_one_div]
    using hN n ((le_max_right _ _).trans hn)

lemma nat_rpow_neg_three_halves_isBigO_inverse :
    (fun n : ℕ ↦ (n : ℝ) ^ (-3 / 2 : ℝ)) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)) := by
  apply Asymptotics.IsBigO.of_norm_eventuallyLE
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (-3 / 2 : ℝ) ≤ -1)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    abs_of_nonneg (show (0 : ℝ) ≤ 1 / (n : ℝ) by positivity), Real.rpow_neg_one, one_div] using h

/-- The sharp leading term in the reducibility probability, with O(1/n) error. -/
theorem binaryProbability_reducible_asymptotic :
    (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      Real.sqrt (2 / (Real.pi * (n : ℝ)))) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)) := by
  have h := binaryProbability_reducible_excess_isBigO.add
    (binaryProbability_minus_one_asymptotic.trans nat_rpow_neg_three_halves_isBigO_inverse)
  simpa only [Pi.add_apply, sub_add_sub_cancel] using h

lemma tendsto_reducible_probability :
    Tendsto (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat) atTop (𝓝 0) := by
  have he := binaryProbability_reducible_excess_isBigO.trans_tendsto
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  simpa only [sub_add_cancel, add_zero] using he.add tendsto_minus_one_probability

/-- The Odlyzko–Poonen irreducibility limit for the actual uniform degree-n family. -/
theorem odlyzko_poonen_irreducibility :
    Tendsto (fun n : ℕ ↦ binaryProbability (n - 1)
      (fun P ↦ Irreducible (P.map (Int.castRingHom ℚ)))) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ 1 - binaryProbability (n - 1) ReducibleOverRat)
      atTop (𝓝 ((1 : ℝ) - 0)) := tendsto_const_nhds.sub tendsto_reducible_probability
  simpa only [binaryProbability_irreducible_eq_one_sub_reducible, sub_zero] using h

end OdlyzkoPoonen
