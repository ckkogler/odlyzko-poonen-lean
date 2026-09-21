import OdlyzkoPoonen.Asymptotics.CentralBinomialCorrection

/-!
# Quantitative second-order central-binomial estimates

Adding a reciprocal correction to the normalized square produces monotone
sequences with limit one. Comparing them with that limit gives the first
correction and a uniform quadratic remainder.
-/

namespace OdlyzkoPoonen
open Filter
open scoped Topology

lemma tendsto_quarter_reciprocal_shift (a : ℝ) :
    Tendsto (fun n : ℕ ↦ 1 / (4 * ((n : ℝ) + a))) atTop (𝓝 0) :=
  (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
    ((tendsto_atTop_add_const_right _ a tendsto_natCast_atTop_atTop).const_mul_atTop
      (by norm_num : (0 : ℝ) < 4))

lemma normalizedCentralBinomialSquare_correction_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 - 1 / (4 * (n : ℝ)) ≤ normalizedCentralBinomialSquare n ∧
      normalizedCentralBinomialSquare n ≤ 1 - 1 / (4 * ((n : ℝ) + 1)) := by
  have hu : Antitone (fun k : ℕ ↦ normalizedCentralBinomialSquare (k + 1) +
      1 / (4 * ((k : ℝ) + 1))) := by
    apply antitone_nat_of_succ_le
    intro k
    have h := normalizedCentralBinomialSquare_step_upper (n := k + 1) (by omega)
    push_cast at h ⊢
    linarith
  have hl : Monotone (fun k : ℕ ↦ normalizedCentralBinomialSquare (k + 1) +
      1 / (4 * ((k : ℝ) + 2))) := by
    apply monotone_nat_of_le_succ
    intro k
    have h := normalizedCentralBinomialSquare_step_lower (k + 1)
    norm_num [Nat.cast_add, Nat.cast_one, add_assoc] at h ⊢
    linarith
  have htu : Tendsto (fun k : ℕ ↦ normalizedCentralBinomialSquare (k + 1) +
      1 / (4 * ((k : ℝ) + 1))) atTop (𝓝 1) := by
    simpa only [add_zero] using
      tendsto_normalizedCentralBinomialSquare.add (tendsto_quarter_reciprocal_shift 1)
  have htl : Tendsto (fun k : ℕ ↦ normalizedCentralBinomialSquare (k + 1) +
      1 / (4 * ((k : ℝ) + 2))) atTop (𝓝 1) := by
    simpa only [add_zero] using
      tendsto_normalizedCentralBinomialSquare.add (tendsto_quarter_reciprocal_shift 2)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hu' := hu.le_of_tendsto (b := k) htu
  have hl' := hl.ge_of_tendsto (b := k) htl
  norm_num [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_assoc] at hu' hl' ⊢
  constructor <;> linarith

/-- The normalized square is `1 - 1/(4*n) + O(1/n^2)` with a finite bound. -/
theorem normalizedCentralBinomialSquare_first_correction {n : ℕ} (hn : 1 ≤ n) :
    |normalizedCentralBinomialSquare n - (1 - 1 / (4 * (n : ℝ)))| ≤
      1 / (4 * (n : ℝ) ^ 2) := by
  obtain ⟨hl, hu⟩ := normalizedCentralBinomialSquare_correction_bounds hn
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : 1 / (4 * (n : ℝ)) - 1 / (4 * ((n : ℝ) + 1)) ≤
      1 / (4 * (n : ℝ) ^ 2) := by
    field_simp
    nlinarith
  linarith

end OdlyzkoPoonen
