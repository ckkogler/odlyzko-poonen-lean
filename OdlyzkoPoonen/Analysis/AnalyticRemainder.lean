import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-!
# Uniform analytic remainders on compact sets

A local power bound for a continuous remainder extends over any fixed compact
set. A function vanishing to a specified order has zero homogeneous terms
below that order. These facts allow analytic amplitudes to be integrated
against a concentrating Gaussian with uniform polynomial error bounds.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
lemma norm_pow_isBigO_at_zero {m n : ℕ} (hmn : m ≤ n) :
    (fun x : V ↦ ‖x‖ ^ n) =O[𝓝 0] (fun x : V ↦ ‖x‖ ^ m) := by
  apply Asymptotics.IsBigO.of_norm_eventuallyLE
  have he : ∀ᶠ x : V in 𝓝 0, ‖x‖ < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : V) (by norm_num : (0 : ℝ) < 1)] with x hx
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  filter_upwards [he] with x hx
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact pow_le_pow_of_le_one (norm_nonneg _) hx.le hmn

omit [NormedSpace ℝ V] in
lemma compact_power_bound_of_local {K : Set V} {h : V → ℝ}
    (hK : IsCompact K) (hh : ContinuousOn h K) (N : ℕ)
    (hloc : h =O[𝓝 0] (fun x : V ↦ ‖x‖ ^ N)) :
    ∃ C > 0, ∀ x ∈ K, |h x| ≤ C * ‖x‖ ^ N := by
  obtain ⟨A, hA, hlocal⟩ := hloc.exists_pos
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hlocal.bound
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hh
  refine ⟨A + |B| / ε ^ N, by positivity, ?_⟩
  intro x hx
  by_cases hnear : ‖x‖ < ε
  · have hlocalx := hball (by simpa only [dist_zero_right] using hnear)
    have hn0 := pow_nonneg (norm_nonneg x) N
    have hb0 : 0 ≤ |B| / ε ^ N := by positivity
    have h' : |h x| ≤ A * ‖x‖ ^ N := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hn0] using hlocalx
    nlinarith
  · have hnorm : ε ^ N ≤ ‖x‖ ^ N := pow_le_pow_left₀ hε.le (le_of_not_gt hnear) N
    have hb : |h x| ≤ |B| := by
      have hb' : |h x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x hx
      exact hb'.trans (le_abs_self B)
    have hscale : |B| ≤ (|B| / ε ^ N) * ‖x‖ ^ N := by
      calc
        _ = (|B| / ε ^ N) * ε ^ N := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity)
    have hAn : 0 ≤ A * ‖x‖ ^ N := by positivity
    nlinarith

/-- A compactly uniform bound for each analytic Taylor remainder. -/
theorem analytic_partialSum_compact_remainder {K : Set V} {f : V → ℝ}
    {p : FormalMultilinearSeries ℝ V ℝ} (hK : IsCompact K)
    (hfK : ContinuousOn f K) (hf : HasFPowerSeriesAt f p 0) (N : ℕ) :
    ∃ C > 0, ∀ x ∈ K, |f x - p.partialSum N x| ≤ C * ‖x‖ ^ N := by
  apply compact_power_bound_of_local hK
    (hfK.sub (p.partialSum_continuous N).continuousOn) N
  simpa only [zero_add] using! hf.isBigO_sub_partialSum_pow N

/-- Polynomial-order vanishing kills every lower homogeneous term. -/
theorem analytic_homogeneous_term_eq_zero_of_isBigO {f : V → ℝ}
    {p : FormalMultilinearSeries ℝ V ℝ} (hf : HasFPowerSeriesAt f p 0)
    {N : ℕ} (hvan : f =O[𝓝 0] (fun x : V ↦ ‖x‖ ^ N)) :
    ∀ j, j < N → ∀ x : V, (p j fun _ ↦ x) = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj x
    have hsum : p.partialSum (j + 1) = fun y ↦ p j (fun _ ↦ y) := by
      funext y
      refine Finset.sum_eq_single j (fun b hb hbj ↦ ?_) (fun hj' ↦ ?_)
      · have hbj' : b < j := by have := Finset.mem_range.mp hb; omega
        exact ih b hbj' (by omega) y
      · exact False.elim (hj' (Finset.mem_range.mpr (by omega)))
    have hr := hf.isBigO_sub_partialSum_pow (j + 1)
    simp only [zero_add, hsum] at hr
    have hterm := (hvan.trans (norm_pow_isBigO_at_zero (by omega : j + 1 ≤ N))).sub hr
    have hp : (fun y : V ↦ p j (fun _ ↦ y)) =O[𝓝 0]
        (fun y : V ↦ ‖y‖ ^ (j + 1)) := by
      simpa only [sub_sub_cancel] using! hterm
    exact hp.continuousMultilinearMap_apply_eq_zero x

end OdlyzkoPoonen
