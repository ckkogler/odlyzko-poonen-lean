import OdlyzkoPoonen.Probability.CyclotomicDegreeTwo

/-!
# Cyclotomic divisors between degree three and a cutoff

There are at most `2*L^2` possible orders below degree `L`. Once the common
atom scale `8*L/sqrt(n)` is at most one, every exponent of degree at least
three is bounded by its cube. Counting the orders gives an explicit fifth
power of the cutoff divided by `n*sqrt(n)`.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical

lemma binaryProbability_cyclotomic_intermediate_fixed_le {n k L : ℕ}
    (hn : 1 ≤ n) (hk : 3 ≤ k.totient) (hkL : k.totient < L)
    (hsmall : 8 * (L : ℝ) / Real.sqrt (n : ℝ) ≤ 1) :
    binaryProbability (n - 1) (fun p ↦ cyclotomic k ℤ ∣ p) ≤
      (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ 3 := by
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

lemma binaryProbability_cyclotomic_intermediate_le {n L : ℕ} (hn : 1 ≤ n)
    (hsmall : 8 * (L : ℝ) / Real.sqrt (n : ℝ) ≤ 1) :
    binaryProbability (n - 1)
      (fun p ↦ ∃ k, 3 ≤ k.totient ∧ k.totient < L ∧ cyclotomic k ℤ ∣ p) ≤
      1024 * (L : ℝ) ^ 5 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
  let s := (Finset.Icc 1 (2 * L ^ 2)).filter
    (fun k : ℕ ↦ 3 ≤ k.totient ∧ k.totient < L)
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
    _ ≤ (s.card : ℝ) * (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ 3 := by
      apply uniformProbability_exists_mem_le_card_mul
      intro k hk
      have h := (Finset.mem_filter.mp hk).2
      exact binaryProbability_cyclotomic_intermediate_fixed_le hn h.1 h.2 hsmall
    _ ≤ (2 * (L : ℝ) ^ 2) * (8 * (L : ℝ) / Real.sqrt (n : ℝ)) ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hc
    _ = _ := residue_order_count_mul_cube (by exact_mod_cast (show 0 < n by omega))

end OdlyzkoPoonen
