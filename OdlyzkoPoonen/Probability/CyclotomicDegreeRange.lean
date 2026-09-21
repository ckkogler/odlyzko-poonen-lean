import OdlyzkoPoonen.Probability.CyclotomicRangeSum

/-!
# Cyclotomic probability bounds above an arbitrary degree

The degree threshold is a parameter rather than a fixed value. This preserves
the power of the atom bound needed to discard large cyclotomic degrees in finer
asymptotic expansions.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical

lemma binaryProbability_cyclotomic_degree_range_fixed_le {n k L D : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D) (hk : D ≤ k.totient) (hkL : k.totient < L)
    (hsmall : 8 * (L : ℝ) / Real.sqrt (n : ℝ) ≤ 1) :
    binaryProbability (n - 1) (fun p ↦ cyclotomic k ℤ ∣ p) ≤
      (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ D := by
  have hk0 : 0 < k := Nat.totient_pos.mp (by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have horder : k ≤ 2 * L ^ 2 := by
    calc
      _ ≤ 2 * k.totient ^ 2 := order_le_two_totient_sq k
      _ ≤ _ := by gcongr
  have hbase : 4 / Real.sqrt ((n : ℝ) / k) ≤ 8 * (L : ℝ) / Real.sqrt (n : ℝ) :=
    residue_atom_scale_le_cutoff hnR hkR (Nat.cast_nonneg L) (by exact_mod_cast horder)
  calc
    _ ≤ (4 / Real.sqrt ((n : ℝ) / k)) ^ k.totient :=
      binaryProbability_cyclotomic_residue_bound_degree hn hk0
    _ ≤ (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ k.totient := by gcongr
    _ ≤ _ := pow_le_pow_of_le_one (by positivity) hsmall hk

/-- Uniform finite bound for all cyclotomic degrees in `[D,L)`. -/
theorem binaryProbability_cyclotomic_degree_range_le {n L D : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D)
    (hsmall : 8 * (L : ℝ) / Real.sqrt (n : ℝ) ≤ 1) :
    binaryProbability (n - 1)
      (fun p ↦ ∃ k, D ≤ k.totient ∧ k.totient < L ∧ cyclotomic k ℤ ∣ p) ≤
      2 * (L : ℝ) ^ 2 * (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ D := by
  let s := (Finset.Icc 1 (2 * L ^ 2)).filter
    (fun k : ℕ ↦ D ≤ k.totient ∧ k.totient < L)
  have hc : s.card ≤ 2 * L ^ 2 := by
    calc
      _ ≤ (Finset.Icc 1 (2 * L ^ 2)).card := Finset.card_filter_le _ _
      _ = _ := by simp
  calc
    _ ≤ uniformProbability (fun w : Fin (n - 1) → Bool ↦
        ∃ k ∈ s, cyclotomic k ℤ ∣ wordPolynomial w) := by
      apply uniformProbability_mono
      rintro w ⟨k, hk, hkL, hd⟩
      have hk0 : 0 < k := Nat.totient_pos.mp (by omega)
      have ho : k ≤ 2 * L ^ 2 := by
        calc
          _ ≤ 2 * k.totient ^ 2 := order_le_two_totient_sq k
          _ ≤ _ := by gcongr
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk0, ho⟩, hk, hkL⟩, hd⟩
    _ ≤ (s.card : ℝ) * (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ D := by
      apply uniformProbability_exists_mem_le_card_mul
      intro k hk
      have h := (Finset.mem_filter.mp hk).2
      exact binaryProbability_cyclotomic_degree_range_fixed_le hn hD h.1 h.2 hsmall
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hc

/-- A cutoff bound covering every order whose cyclotomic degree is at least `D`. -/
theorem binaryProbability_cyclotomic_degree_at_least_le {n L D : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D)
    (hsmall : 8 * (L : ℝ) / Real.sqrt (n : ℝ) ≤ 1) :
    binaryProbability (n - 1)
      (fun p ↦ ∃ k, D ≤ k.totient ∧ cyclotomic k ℤ ∣ p) ≤
      2 * (L : ℝ) ^ 2 * (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ D +
        4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ L := by
  let E := fun p : ℤ[X] ↦ ∃ k, D ≤ k.totient ∧ k.totient < L ∧ cyclotomic k ℤ ∣ p
  let F := fun p : ℤ[X] ↦ ∃ k, 0 < k ∧ L ≤ k.totient ∧ cyclotomic k ℤ ∣ p
  calc
    _ ≤ binaryProbability (n - 1) (fun p ↦ E p ∨ F p) := by
      apply uniformProbability_mono
      rintro w ⟨k, hk, hd⟩
      by_cases hL : k.totient < L
      · exact Or.inl ⟨k, hk, hL, hd⟩
      · exact Or.inr ⟨k, Nat.totient_pos.mp (by omega), by omega, hd⟩
    _ ≤ binaryProbability (n - 1) E + binaryProbability (n - 1) F :=
      binaryProbability_or_le_add _ E F
    _ ≤ _ := add_le_add (binaryProbability_cyclotomic_degree_range_le hn hD hsmall)
      (binaryProbability_high_cyclotomic_le hn L)

end OdlyzkoPoonen
