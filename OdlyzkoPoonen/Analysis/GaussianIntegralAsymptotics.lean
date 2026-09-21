import OdlyzkoPoonen.Analysis.GaussianIntegralBounds
import OdlyzkoPoonen.Analysis.AnalyticRemainder

/-!
# Asymptotic Gaussian remainder estimates

Local polynomial remainders and tails outside a fixed neighborhood have the
same decay rate after integration. Continuous multilinear amplitudes give
the homogeneous coefficients in the resulting expansion.
-/

namespace OdlyzkoPoonen
open MeasureTheory Filter Asymptotics
open scoped Topology BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem gaussian_weighted_remainder_isBigO {K : Set V} (hK : MeasurableSet K)
    {h Q : V → ℝ} (N : ℕ) {C b : ℝ} (hC : 0 ≤ C) (hb : 0 < b)
    (hh : ∀ x ∈ K, |h x| ≤ C * ‖x‖ ^ N)
    (hQ : ∀ x ∈ K, b * ‖x‖ ^ 2 ≤ Q x) :
    (fun n : ℕ ↦ ∫ x in K, h x * Real.exp (-(n : ℝ) * Q x)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-((Module.finrank ℝ V : ℝ) + N) / 2)) := by
  let J := ∫ x : V, ‖x‖ ^ N * Real.exp (-b * ‖x‖ ^ 2)
  refine isBigO_iff.mpr ⟨C * J, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  simp only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
  have hbound := abs_setIntegral_le_gaussian_moment hK N hC hb hn0
    (f := fun x ↦ h x * Real.exp (-(n : ℝ) * Q x)) (fun x hx ↦ by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        _ ≤ (C * ‖x‖ ^ N) * Real.exp (-((n : ℝ) * b) * ‖x‖ ^ 2) := by
          apply mul_le_mul (hh x hx) _ (Real.exp_pos _).le (by positivity)
          apply Real.exp_le_exp.mpr
          nlinarith [hQ x hx]
        _ = _ := by ring)
  convert hbound using 1; dsimp [J]; ring

theorem gaussian_tail_isBigO {K : Set V} (hK : MeasurableSet K)
    {h Q : V → ℝ} {ε b C : ℝ} (hε : 0 < ε) (hb : 0 < b) (hC : 0 ≤ C)
    (j N : ℕ) (hj : j ≤ N) (hball : Metric.ball 0 ε ⊆ K)
    (hh : ∀ x, |h x| ≤ C * ‖x‖ ^ j)
    (hQ : ∀ x, b * ‖x‖ ^ 2 ≤ Q x) :
    (fun n : ℕ ↦ ∫ x in Kᶜ, h x * Real.exp (-(n : ℝ) * Q x)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-((Module.finrank ℝ V : ℝ) + N) / 2)) := by
  let J := ∫ x : V, ‖x‖ ^ N * Real.exp (-b * ‖x‖ ^ 2)
  refine isBigO_iff.mpr ⟨(C * (ε ^ (N - j))⁻¹) * J, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  simp only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
  have hbound := abs_gaussian_tail_le hK hε hb hC hn0 j N hj hball hh hQ
  convert hbound using 1; dsimp [J]; ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma multilinear_diagonal_bound {j : ℕ} (p : V [×j]→L[ℝ] ℝ) (x : V) :
    |p (fun _ ↦ x)| ≤ ‖p‖ * ‖x‖ ^ j := by
  simpa only [Real.norm_eq_abs, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    using p.le_opNorm (fun _ ↦ x)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma multilinear_diagonal_homogeneous {j : ℕ} (p : V [×j]→L[ℝ] ℝ) (t : ℝ) (x : V) :
    p (fun _ ↦ t • x) = t ^ j * p (fun _ ↦ x) := by
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    using p.map_smul_univ (fun _ ↦ t) (fun _ ↦ x)

lemma integrable_multilinear_gaussian {j : ℕ} (p : V [×j]→L[ℝ] ℝ)
    {Q : V → ℝ} (hQ : Continuous Q) {b : ℝ} (hb : 0 < b)
    (hcoercive : ∀ x, b * ‖x‖ ^ 2 ≤ Q x) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x ↦ p (fun _ ↦ x) * Real.exp (-r * Q x)) := by
  have hc : Continuous (fun x : V ↦ p (fun _ ↦ x)) := by fun_prop
  have hi := integrable_polynomial_growth_mul_gaussian hc
    (show Continuous (fun x ↦ r * Q x) by fun_prop) (mul_pos hr hb) j
    (multilinear_diagonal_bound p) (fun x ↦ by nlinarith [hcoercive x])
  simpa only [neg_mul] using hi

lemma multilinear_gaussian_integral {j : ℕ} (p : V [×j]→L[ℝ] ℝ)
    {Q : V → ℝ} (hQ : ∀ (t : ℝ), 0 < t → ∀ x, Q (t • x) = t ^ 2 * Q x)
    {r : ℝ} (hr : 0 < r) :
    (∫ x : V, p (fun _ ↦ x) * Real.exp (-r * Q x)) =
      r ^ (-((Module.finrank ℝ V : ℝ) + j) / 2) *
        ∫ x : V, p (fun _ ↦ x) * Real.exp (-Q x) :=
  homogeneous_gaussian_integral_half_power j
    (fun t _ x ↦ multilinear_diagonal_homogeneous p t x) hQ hr

end OdlyzkoPoonen
