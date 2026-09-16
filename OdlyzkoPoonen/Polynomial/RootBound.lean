import OdlyzkoPoonen.Polynomial.Binary
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A strict radius-two root bound

For a monic complex polynomial whose lower coefficients have norm at most one,
a root of norm at least two would make the leading term strictly larger than
the sum of the lower terms. The finite geometric inequality is strict even at
radius two. Binary integer polynomials, and the roots of all their divisors,
therefore satisfy the strict bound.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

lemma sum_range_pow_lt_pow_of_two_le {r : ℝ} (hr : 2 ≤ r) (n : ℕ) :
    (∑ i ∈ Finset.range n, r ^ i) < r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hr0 : 0 ≤ r := by linarith
    have hmul := mul_le_mul_of_nonneg_left hr (pow_nonneg hr0 n)
    nlinarith

lemma monic_root_norm_lt_two {p : ℂ[X]} (hp : p.Monic)
    (hc : ∀ k < p.natDegree, ‖p.coeff k‖ ≤ 1) {z : ℂ} (hz : p.eval z = 0) :
    ‖z‖ < 2 := by
  have he : (∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i) + z ^ p.natDegree = 0 := by
    rw [← hz, eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul]
  have hs : (∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i) = -z ^ p.natDegree :=
    eq_neg_of_add_eq_zero_left he
  have hle : ‖z‖ ^ p.natDegree ≤ ∑ i ∈ Finset.range p.natDegree, ‖z‖ ^ i := by
    calc
      _ = ‖∑ i ∈ Finset.range p.natDegree, p.coeff i * z ^ i‖ := by
        rw [hs, norm_neg, norm_pow]
      _ ≤ ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, norm_pow]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hc i (Finset.mem_range.mp hi))
            (pow_nonneg (norm_nonneg z) i)
  by_contra hn
  exact (not_lt_of_ge hle) (sum_range_pow_lt_pow_of_two_le (le_of_not_gt hn) p.natDegree)

lemma HasBinaryEndpoints.root_norm_lt_two {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) {z : ℂ} (hz : p.eval₂ (Int.castRingHom ℂ) z = 0) :
    ‖z‖ < 2 := by
  apply monic_root_norm_lt_two (hp.monic.map (Int.castRingHom ℂ))
  · intro k _
    rw [coeff_map]
    rcases hp.binary k with hk | hk <;> simp [hk]
  · simpa only [eval_map] using hz

lemma HasBinaryEndpoints.divisor_root_norm_lt_two {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hdvd : J ∣ p) {z : ℂ}
    (hz : J.eval₂ (Int.castRingHom ℂ) z = 0) : ‖z‖ < 2 := by
  apply hp.root_norm_lt_two
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, eval₂_mul, hz, zero_mul]

end OdlyzkoPoonen
