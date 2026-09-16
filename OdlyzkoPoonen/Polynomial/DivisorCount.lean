import OdlyzkoPoonen.Polynomial.BoundedMonicFamily
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Counting possible small-degree divisors

The coefficient bounds give an explicit finite pool containing every monic
nonconstant divisor of degree at most `L`. Its cardinality is bounded by the
source's sum `∑ h=1..L, (2*3^h+1)^h`, and that sum is at most `exp(4*L^2)`.
The pool depends only on `L`, not on the original polynomial or its degree.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma bounded_coefficient_choices_le_three_pow (h : ℕ) :
    (2 * (3 : ℝ) ^ h + 1) ^ h ≤ (3 : ℝ) ^ ((h + 1) * h) := by
  calc
    _ ≤ ((3 : ℝ) ^ (h + 1)) ^ h := by
      apply pow_le_pow_left₀ (by positivity)
      rw [pow_succ]
      have hpow : (1 : ℝ) ≤ 3 ^ h := one_le_pow₀ (by norm_num)
      nlinarith
    _ = _ := (pow_mul _ _ _).symm

lemma divisor_count_summand_le_exp {h L : ℕ} (hh : 1 ≤ h) (hL : h ≤ L) :
    (2 * (3 : ℝ) ^ h + 1) ^ h ≤ Real.exp (3 * (L : ℝ) ^ 2) := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hLR : (h : ℝ) ≤ L := by exact_mod_cast hL
  have hprod : (((h + 1) * h : ℕ) : ℝ) ≤ 2 * (L : ℝ) ^ 2 := by
    push_cast
    have hsq := mul_le_mul hLR hLR (Nat.cast_nonneg h) (Nat.cast_nonneg L)
    nlinarith [sq_nonneg ((h : ℝ) - 1)]
  have hlog : Real.log 3 ≤ 3 / 2 := by linarith [Real.log_three_lt_d9]
  calc
    _ ≤ (3 : ℝ) ^ ((h + 1) * h) := bounded_coefficient_choices_le_three_pow h
    _ = Real.exp (((h + 1) * h : ℕ) * Real.log 3) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (3 * (L : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ (((h + 1) * h : ℕ) : ℝ) * (3 / 2) :=
          mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
        _ ≤ _ := by nlinarith

lemma sum_divisor_counts_le_exp (L : ℕ) :
    (∑ h ∈ Finset.Icc 1 L, (2 * (3 : ℝ) ^ h + 1) ^ h) ≤
      Real.exp (4 * (L : ℝ) ^ 2) := by
  have hLe : (L : ℝ) ≤ Real.exp ((L : ℝ) ^ 2) := by
    calc
      _ ≤ (L : ℝ) ^ 2 + 1 := by nlinarith [sq_nonneg ((L : ℝ) - 1), show (0 : ℝ) ≤ L from Nat.cast_nonneg L]
      _ ≤ _ := Real.add_one_le_exp _
  calc
    _ ≤ ∑ _h ∈ Finset.Icc 1 L, Real.exp (3 * (L : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro h hh
      exact divisor_count_summand_le_exp (Finset.mem_Icc.mp hh).1 (Finset.mem_Icc.mp hh).2
    _ = (L : ℝ) * Real.exp (3 * (L : ℝ) ^ 2) := by simp
    _ ≤ Real.exp ((L : ℝ) ^ 2) * Real.exp (3 * (L : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hLe (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- A uniform finite pool of possible nonconstant monic divisors up to degree `L`. -/
noncomputable def smallDivisorCandidates (L : ℕ) : Finset ℤ[X] :=
  (Finset.Icc 1 L).biUnion (fun h ↦ boundedMonicFamily h (3 ^ h))

lemma HasBinaryEndpoints.monic_divisor_mem_candidates {n L : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p)
    (hpos : 1 ≤ J.natDegree) (hL : J.natDegree ≤ L) : J ∈ smallDivisorCandidates L := by
  exact Finset.mem_biUnion.mpr ⟨J.natDegree, Finset.mem_Icc.mpr ⟨hpos, hL⟩,
    hp.monic_divisor_mem_boundedFamily hJ hdvd⟩

lemma card_smallDivisorCandidates_le_sum (L : ℕ) :
    (smallDivisorCandidates L).card ≤ ∑ h ∈ Finset.Icc 1 L, (2 * 3 ^ h + 1) ^ h := by
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum (fun h _ ↦ card_boundedMonicFamily_le h (3 ^ h)))

lemma card_smallDivisorCandidates_le_exp (L : ℕ) :
    ((smallDivisorCandidates L).card : ℝ) ≤ Real.exp (4 * (L : ℝ) ^ 2) := by
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 L, (2 * (3 : ℝ) ^ h + 1) ^ h := by
      exact_mod_cast card_smallDivisorCandidates_le_sum L
    _ ≤ _ := sum_divisor_counts_le_exp L

end OdlyzkoPoonen
