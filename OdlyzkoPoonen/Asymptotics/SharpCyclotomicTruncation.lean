import OdlyzkoPoonen.Asymptotics.FiniteCyclotomicApproximation

/-!
# Sharp fixed-degree cyclotomic truncation

The finitely many orders at the boundary degree can be estimated separately.
This removes the logarithmic loss and gives `O(n⁻ᴿ)` already at degree `2R`.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics
open scoped Classical

lemma eventually_fixed_residue_scale_le_one (L : ℕ) :
    ∀ᶠ n : ℕ in atTop, 8 * (L : ℝ) / Real.sqrt (n : ℝ) ≤ 1 := by
  filter_upwards [eventually_ge_atTop (64 * L ^ 2 + 1)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbound : 64 * (L : ℝ) ^ 2 + 1 ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  rw [div_le_one (Real.sqrt_pos.mpr hn0)]
  nlinarith [Real.sqrt_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) L]

lemma binaryProbability_cyclotomic_fixed_degree_range_isBigO
    (R L : ℕ) (hR : 1 ≤ R) :
    (fun n : ℕ ↦ binaryProbability (n - 1)
      (fun p ↦ ∃ k, 2 * R ≤ k.totient ∧ k.totient < L ∧ cyclotomic k ℤ ∣ p))
      =O[atTop] (fun n : ℕ ↦ ((n : ℝ) ^ R)⁻¹) := by
  refine isBigO_iff.mpr ⟨2 * (L : ℝ) ^ 2 * (8 * (L : ℝ)) ^ (2 * R), ?_⟩
  filter_upwards [eventually_ge_atTop 1, eventually_fixed_residue_scale_le_one L]
    with n hn hsmall
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := binaryProbability_cyclotomic_degree_range_le hn
    (show 1 ≤ 2 * R by omega) hsmall
  have hp0 : 0 ≤ binaryProbability (n - 1)
      (fun p ↦ ∃ k, 2 * R ≤ k.totient ∧ k.totient < L ∧ cyclotomic k ℤ ∣ p) :=
    uniformProbability_nonneg _
  simp only [Real.norm_eq_abs, abs_of_nonneg hp0,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hn0.le R))]
  have hden : Real.sqrt (n : ℝ) ^ (2 * R) = (n : ℝ) ^ R := by
    rw [pow_mul, Real.sq_sqrt hn0.le]
  convert h using 1
  rw [div_pow, hden]
  ring

/-- The degree threshold `2R` suffices for an error of order `n⁻ᴿ`. -/
theorem binaryProbability_cyclotomic_sharp_degree_tail_isBigO
    (R : ℕ) (hR : 1 ≤ R) :
    (fun n : ℕ ↦ binaryProbability (n - 1)
      (fun p ↦ ∃ k, 2 * R ≤ k.totient ∧ cyclotomic k ℤ ∣ p)) =O[atTop]
      (fun n : ℕ ↦ ((n : ℝ) ^ R)⁻¹) := by
  have h := (binaryProbability_cyclotomic_fixed_degree_range_isBigO R (2 * R + 1) hR).add
    (binaryProbability_cyclotomic_degree_tail_isBigO R)
  refine (Asymptotics.IsBigO.of_norm_eventuallyLE ?_).trans h
  apply Filter.Eventually.of_forall
  intro n
  have hp0 : 0 ≤ binaryProbability (n - 1)
      (fun p ↦ ∃ k, 2 * R ≤ k.totient ∧ cyclotomic k ℤ ∣ p) :=
    uniformProbability_nonneg _
  have hs0 : 0 ≤ binaryProbability (n - 1)
      (fun p ↦ ∃ k, 2 * R ≤ k.totient ∧ k.totient < 2 * R + 1 ∧ cyclotomic k ℤ ∣ p) +
      binaryProbability (n - 1)
        (fun p ↦ ∃ k, 2 * R + 1 ≤ k.totient ∧ cyclotomic k ℤ ∣ p) :=
    add_nonneg (uniformProbability_nonneg _) (uniformProbability_nonneg _)
  simp only [Real.norm_eq_abs, abs_of_nonneg hp0]
  calc
    _ ≤ binaryProbability (n - 1) (fun p ↦
        (∃ k, 2 * R ≤ k.totient ∧ k.totient < 2 * R + 1 ∧ cyclotomic k ℤ ∣ p) ∨
        (∃ k, 2 * R + 1 ≤ k.totient ∧ cyclotomic k ℤ ∣ p)) := by
      apply uniformProbability_mono
      rintro w ⟨k, hk, hd⟩
      by_cases hl : k.totient < 2 * R + 1
      · exact Or.inl ⟨k, hk, hl, hd⟩
      · exact Or.inr ⟨k, by omega, hd⟩
    _ ≤ _ := binaryProbability_or_le_add _ _ _

/-- A fixed union below degree `2R` approximates reducibility to order `n⁻ᴿ`. -/
theorem binaryProbability_reducible_sharp_finite_cyclotomic_approximation
    (R : ℕ) (hR : 1 ≤ R) :
    (fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (HasBoundedDegreeCyclotomicDivisor (2 * R)))
      =O[atTop] (fun n : ℕ ↦ ((n : ℝ) ^ R)⁻¹) := by
  have hnoncyc : (fun n : ℕ ↦ binaryProbability (n - 1)
      (fun p ↦ ReducibleOverRat p ∧ ¬ HasCyclotomicDivisor p)) =O[atTop]
      (fun n : ℕ ↦ ((n : ℝ) ^ R)⁻¹) := by
    have hpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
    simpa only [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_natCast] using
      binaryProbability_reducible_noncyclotomic_isBigO (R : ℝ) hpos
  have h := hnoncyc.add (binaryProbability_cyclotomic_sharp_degree_tail_isBigO R hR)
  refine (Asymptotics.IsBigO.of_norm_eventuallyLE ?_).trans h
  filter_upwards [eventually_ge_atTop (2 * R)] with n hn
  have hn1 : 1 ≤ n := by omega
  have he0 : 0 ≤ binaryProbability (n - 1) ReducibleOverRat -
      binaryProbability (n - 1) (HasBoundedDegreeCyclotomicDivisor (2 * R)) := by
    rw [reducible_sub_bounded_cyclotomic_probability_eq hn1 hn]
    exact uniformProbability_nonneg _
  have hs0 : 0 ≤ binaryProbability (n - 1)
      (fun p ↦ ReducibleOverRat p ∧ ¬ HasCyclotomicDivisor p) +
      binaryProbability (n - 1)
        (fun p ↦ ∃ k, 2 * R ≤ k.totient ∧ cyclotomic k ℤ ∣ p) :=
    add_nonneg (uniformProbability_nonneg _) (uniformProbability_nonneg _)
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg he0, abs_of_nonneg hs0]
    using reducible_sub_bounded_cyclotomic_probability_le hn1 hn

end OdlyzkoPoonen
