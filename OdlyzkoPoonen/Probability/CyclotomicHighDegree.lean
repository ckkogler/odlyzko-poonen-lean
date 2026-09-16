import OdlyzkoPoonen.Arithmetic.TotientOrder
import OdlyzkoPoonen.Probability.IntegerDivisibility
import OdlyzkoPoonen.Probability.FiniteSetUnion
import OdlyzkoPoonen.Polynomial.CyclotomicDivisors

/-!
# The high-degree cyclotomic tail

A cyclotomic divisor of a degree-`n` sample has degree at most `n` and order at
most `2*n^2`. Reduction modulo two bounds each fixed divisor by `2/2^degree`.
Consequently all cyclotomic divisors of degree at least `L` have total
probability at most `4*n^2/2^L`, uniformly in the order and the cutoff.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma HasBinaryEndpoints.cyclotomic_order_le {n k : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hd : cyclotomic k ℤ ∣ p) : k ≤ 2 * n ^ 2 := by
  have hdegree := natDegree_le_of_dvd hd hp.ne_zero
  rw [natDegree_cyclotomic, hp.degree] at hdegree
  calc
    k ≤ 2 * k.totient ^ 2 := order_le_two_totient_sq k
    _ ≤ _ := by gcongr

lemma binaryProbability_cyclotomic_divisible_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    binaryProbability (n - 1) (fun p ↦ cyclotomic k ℤ ∣ p) ≤
      2 / (2 : ℝ) ^ k.totient := by
  simpa only [natDegree_cyclotomic] using
    binaryProbability_monic_divisible_le hn (cyclotomic.monic k ℤ)

lemma binaryProbability_high_cyclotomic_le {n : ℕ} (hn : 1 ≤ n) (L : ℕ) :
    binaryProbability (n - 1)
      (fun p ↦ ∃ k, 0 < k ∧ L ≤ k.totient ∧ cyclotomic k ℤ ∣ p) ≤
      4 * (n : ℝ) ^ 2 / (2 : ℝ) ^ L := by
  let s := (Finset.Icc 1 (2 * n ^ 2)).filter (fun k ↦ L ≤ k.totient)
  have hc : s.card ≤ 2 * n ^ 2 := by
    calc
      _ ≤ (Finset.Icc 1 (2 * n ^ 2)).card := Finset.card_filter_le _ _
      _ = _ := by simp
  calc
    _ ≤ uniformProbability (fun w : Fin (n - 1) → Bool ↦
        ∃ k ∈ s, cyclotomic k ℤ ∣ wordPolynomial w) := by
      apply uniformProbability_mono
      rintro w ⟨k, hk, hL, hd⟩
      have ho := (wordPolynomial_endpoints w).cyclotomic_order_le hd
      rw [Nat.sub_add_cancel hn] at ho
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk, ho⟩, hL⟩, hd⟩
    _ ≤ (s.card : ℝ) * (2 / (2 : ℝ) ^ L) := by
      apply uniformProbability_exists_mem_le_card_mul
      intro k hk
      have hL := (Finset.mem_filter.mp hk).2
      calc
        _ ≤ 2 / (2 : ℝ) ^ k.totient := binaryProbability_cyclotomic_divisible_le hn k
        _ ≤ _ := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact pow_le_pow_right₀ (by norm_num) hL
    _ ≤ (2 * (n : ℝ) ^ 2) * (2 / (2 : ℝ) ^ L) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hc
    _ = _ := by ring

end OdlyzkoPoonen
