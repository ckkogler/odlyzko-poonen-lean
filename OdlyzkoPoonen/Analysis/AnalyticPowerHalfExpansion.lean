import OdlyzkoPoonen.Analysis.PoweredIntegralExpansion
import OdlyzkoPoonen.Analysis.GaussianMomentPolynomial
import OdlyzkoPoonen.Analysis.HalfPowerTruncation

/-!
# Half-power expansions for analytic powers with Gaussian domination

Quartic agreement with a positive quadratic Gaussian, together with analytic
amplitudes, gives fixed coefficients to every finite order. Polynomial
packaging and truncation make the half-power statement explicit.
-/

namespace OdlyzkoPoonen
open Polynomial MeasureTheory Filter Asymptotics
open scoped Topology BigOperators Classical

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem analytic_power_polynomial_expansion {K L : Set V}
    (hK : MeasurableSet K) (hL : IsCompact L) (hKL : K ⊆ L)
    {ε b C H : ℝ} (hε : 0 < ε) (hb : 0 < b) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hball : Metric.ball 0 ε ⊆ K) {ψ Q h : V → ℝ}
    (hψc : ContinuousOn ψ L) (hQc : Continuous Q) (hhc : ContinuousOn h L)
    (hψa : AnalyticAt ℝ ψ 0) (hQa : AnalyticAt ℝ Q 0) (hha : AnalyticAt ℝ h 0)
    (hQb : ∀ x, b * ‖x‖ ^ 2 ≤ Q x)
    (hQs : ∀ (t : ℝ), 0 < t → ∀ x, Q (t • x) = t ^ 2 * Q x)
    (hψ0 : ∀ x ∈ K, 0 ≤ ψ x)
    (hψ : ∀ x ∈ K, ψ x ≤ Real.exp (-b * ‖x‖ ^ 2))
    (hδ : ∀ x ∈ K, |ψ x - Real.exp (-Q x)| ≤ C * ‖x‖ ^ 4)
    (hδo : (fun x ↦ ψ x - Real.exp (-Q x)) =O[𝓝 0] (fun x : V ↦ ‖x‖ ^ 4))
    (hh : ∀ x ∈ K, |h x| ≤ H) (hd : 0 < Module.finrank ℝ V) (R : ℕ) (hR : 1 ≤ R) :
    ∃ P : ℝ[X], P.coeff 0 = 0 ∧
      (fun n : ℕ ↦ (∫ x in K, h x * ψ x ^ n) - P.eval ((Real.sqrt (n : ℝ))⁻¹))
        =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-(Module.finrank ℝ V : ℝ) / 2 - R)) := by
  choose p hp using fun r : ℕ ↦ poweredGaussianAmplitude_analyticAt hψa hQa hha r
  let c := fun r j ↦ gaussianAmplitudeCoefficient (p r) Q j
  have hc : ∀ r < R, ∀ j < 4 * r, c r j = 0 := by
    intro r _ j hj
    exact gaussianAmplitudeCoefficient_vanishing hQc.continuousAt hha.continuousAt hδo r (hp r) j hj
  refine ⟨gaussianMomentPolynomial (Module.finrank ℝ V) R c,
    gaussianMomentPolynomial_coeff_zero _ _ hd c, ?_⟩
  have he := powered_integral_moment_expansion hK hL hKL hε hb hC hH hball hψc hQc hhc
    hQb hQs hψ0 hψ hδ hh R hR p (fun r _ ↦ hp r)
  apply he.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (max 1 R)] with n hn
  rw [gaussianMomentPolynomial_eval _ _ n c (by omega) (by omega) hc]

/-- An explicit fixed half-power coefficient expansion at any prescribed order. -/
theorem analytic_power_half_expansion {K L : Set V}
    (hK : MeasurableSet K) (hL : IsCompact L) (hKL : K ⊆ L)
    {ε b C H : ℝ} (hε : 0 < ε) (hb : 0 < b) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hball : Metric.ball 0 ε ⊆ K) {ψ Q h : V → ℝ}
    (hψc : ContinuousOn ψ L) (hQc : Continuous Q) (hhc : ContinuousOn h L)
    (hψa : AnalyticAt ℝ ψ 0) (hQa : AnalyticAt ℝ Q 0) (hha : AnalyticAt ℝ h 0)
    (hQb : ∀ x, b * ‖x‖ ^ 2 ≤ Q x)
    (hQs : ∀ (t : ℝ), 0 < t → ∀ x, Q (t • x) = t ^ 2 * Q x)
    (hψ0 : ∀ x ∈ K, 0 ≤ ψ x)
    (hψ : ∀ x ∈ K, ψ x ≤ Real.exp (-b * ‖x‖ ^ 2))
    (hδ : ∀ x ∈ K, |ψ x - Real.exp (-Q x)| ≤ C * ‖x‖ ^ 4)
    (hδo : (fun x ↦ ψ x - Real.exp (-Q x)) =O[𝓝 0] (fun x : V ↦ ‖x‖ ^ 4))
    (hh : ∀ x ∈ K, |h x| ≤ H) (hd : 0 < Module.finrank ℝ V) (R : ℕ) (hR : 1 ≤ R) :
    ∃ c : ℕ → ℝ, c 0 = 0 ∧
      (fun n : ℕ ↦ (∫ x in K, h x * ψ x ^ n) -
        ∑ j ∈ Finset.range (2 * R), c j * (n : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop]
          (fun n : ℕ ↦ (n : ℝ) ^ (-(R : ℝ))) := by
  obtain ⟨P, hP0, hP⟩ := analytic_power_polynomial_expansion hK hL hKL hε hb hC hH hball
    hψc hQc hhc hψa hQa hha hQb hQs hψ0 hψ hδ hδo hh hd R hR
  obtain ⟨hdeg, hcoeff, htail⟩ := polynomial_halfpower_truncation P (2 * R) (by omega)
  let Qp := P %ₘ X ^ (2 * R)
  refine ⟨Qp.coeff, hcoeff.trans hP0, ?_⟩
  have hscale : (fun n : ℕ ↦ (n : ℝ) ^ (-(Module.finrank ℝ V : ℝ) / 2 - R)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(R : ℝ))) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    apply Real.rpow_le_rpow_of_exponent_le hn'
    have := Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ V)
    linarith
  have htail' : (fun n : ℕ ↦ P.eval ((Real.sqrt (n : ℝ))⁻¹) - Qp.eval ((Real.sqrt (n : ℝ))⁻¹))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-(R : ℝ))) := by
    convert htail using 1
    funext n
    congr 1
    push_cast
    ring
  have he := (hP.trans hscale).add htail'
  simpa only [sub_add_sub_cancel, polynomial_eval_inverse_sqrt_eq_half_power_sum Qp hdeg] using he

end OdlyzkoPoonen
