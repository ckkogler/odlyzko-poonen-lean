import OdlyzkoPoonen.Probability.CyclotomicResidueBound
import OdlyzkoPoonen.Probability.CyclotomicHighDegree
import OdlyzkoPoonen.Analysis.AtomScale

/-!
# Cyclotomic divisors of degree two

The elementary totient bound confines these orders to `1,...,8`. Squaring the
fixed-order estimate gives `16*k/n`, so summing all possibilities costs at
most `1024/n`. No classification of the degree-two cyclotomic polynomials is
needed, and impossible small-degree divisors cause no exception.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical

lemma binaryProbability_cyclotomic_degree_two_fixed_le {n k : ℕ} (hn : 1 ≤ n)
    (hk : k.totient = 2) :
    binaryProbability (n - 1) (fun p ↦ cyclotomic k ℤ ∣ p) ≤ 128 / (n : ℝ) := by
  have hk0 : 0 < k := Nat.totient_pos.mp (by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have horder : k ≤ 8 := by simpa [hk] using order_le_two_totient_sq k
  calc
    _ ≤ (4 / Real.sqrt ((n : ℝ) / k)) ^ k.totient :=
      binaryProbability_cyclotomic_residue_bound_degree hn hk0
    _ = 16 * (k : ℝ) / n := by rw [hk, residue_atom_scale_sq hnR hkR]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hnR.le
      have : (k : ℝ) ≤ 8 := by exact_mod_cast horder
      linarith

lemma binaryProbability_cyclotomic_degree_two_le {n : ℕ} (hn : 1 ≤ n) :
    binaryProbability (n - 1) (fun p ↦ ∃ k, k.totient = 2 ∧ cyclotomic k ℤ ∣ p) ≤
      1024 / (n : ℝ) := by
  let s := (Finset.Icc 1 8).filter (fun k : ℕ ↦ k.totient = 2)
  have hc : s.card ≤ 8 := by
    calc
      _ ≤ (Finset.Icc 1 8 : Finset ℕ).card := Finset.card_filter_le _ _
      _ = _ := by norm_num
  calc
    _ ≤ uniformProbability (fun w : Fin (n - 1) → Bool ↦
        ∃ k ∈ s, cyclotomic k ℤ ∣ wordPolynomial w) := by
      apply uniformProbability_mono
      rintro w ⟨k, hk, hd⟩
      have hk0 : 0 < k := Nat.totient_pos.mp (by omega)
      have ho : k ≤ 8 := by simpa [hk] using order_le_two_totient_sq k
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk0, ho⟩, hk⟩, hd⟩
    _ ≤ (s.card : ℝ) * (128 / (n : ℝ)) := by
      apply uniformProbability_exists_mem_le_card_mul
      intro k hk
      exact binaryProbability_cyclotomic_degree_two_fixed_le hn (Finset.mem_filter.mp hk).2
    _ ≤ 8 * (128 / (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hc
    _ = _ := by ring

end OdlyzkoPoonen
