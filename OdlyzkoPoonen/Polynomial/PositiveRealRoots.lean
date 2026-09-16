import OdlyzkoPoonen.Polynomial.Binary
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Positivity and positive roots

Binary endpoint polynomials are at least one on the nonnegative real axis.
Conversely, a monic real polynomial with negative constant coefficient has
positive degree, tends to positive infinity, and has a positive real root by
the intermediate value theorem. These also justify the source's real-root
argument for signs of factor constants, independently of the algebraic proof.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma HasBinaryEndpoints.eval_real_ge_one {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ p.eval₂ (Int.castRingHom ℝ) t := by
  rw [eval₂_eq_sum_range]
  change 1 ≤ ∑ k ∈ Finset.range (p.natDegree + 1), (p.coeff k : ℝ) * t ^ k
  have hs := Finset.single_le_sum
    (f := fun k ↦ (p.coeff k : ℝ) * t ^ k)
    (fun k _ ↦ mul_nonneg (by exact_mod_cast hp.binary.coeff_nonneg k) (pow_nonneg ht k))
    (Finset.mem_range.mpr (Nat.zero_lt_succ p.natDegree))
  simpa only [hp.constant, Int.cast_one, pow_zero, mul_one] using hs

lemma HasBinaryEndpoints.eval_real_pos {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) {t : ℝ} (ht : 0 ≤ t) :
    0 < p.eval₂ (Int.castRingHom ℝ) t :=
  lt_of_lt_of_le (by norm_num) (hp.eval_real_ge_one ht)

lemma monic_exists_positive_root_of_constant_neg {p : ℝ[X]} (hp : p.Monic)
    (h0 : p.coeff 0 < 0) : ∃ t : ℝ, 0 < t ∧ p.eval t = 0 := by
  have hdeg : 0 < p.natDegree := by
    by_contra hn
    have hz : p.natDegree = 0 := by omega
    have hc := hp.coeff_natDegree
    rw [hz] at hc
    rw [hc] at h0
    linarith
  have hlim := p.tendsto_atTop_of_leadingCoeff_nonneg
    (natDegree_pos_iff_degree_pos.mp hdeg) (by rw [hp.leadingCoeff]; norm_num)
  obtain ⟨b, hb⟩ := Filter.Eventually.exists_forall_of_atTop (hlim.eventually_gt_atTop 0)
  have hc0 : (0 : ℝ) ≤ max 1 b := le_trans (by norm_num) (le_max_left 1 b)
  have hce : 0 < p.eval (max 1 b) := hb _ (le_max_right 1 b)
  have he0 : p.eval 0 < 0 := by simpa only [coeff_zero_eq_eval_zero] using h0
  obtain ⟨t, ht, hroot⟩ := intermediate_value_Icc hc0 p.continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (p.eval 0) (p.eval (max 1 b)) from ⟨he0.le, hce.le⟩)
  refine ⟨t, ?_, hroot⟩
  by_contra hpos
  have hz : t = 0 := le_antisymm (le_of_not_gt hpos) ht.1
  rw [hz] at hroot
  linarith

end OdlyzkoPoonen
