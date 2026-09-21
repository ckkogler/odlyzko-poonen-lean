import OdlyzkoPoonen.Analysis.PoweredIntegralExpansion

/-!
# The leading Gaussian coefficient with a full inverse-power improvement

Odd linear amplitudes integrate to zero against an even quadratic Gaussian.
The leading term is therefore the amplitude at zero times the Gaussian volume,
with an error smaller by one full inverse power.
-/

namespace OdlyzkoPoonen
open MeasureTheory Filter Asymptotics
open scoped Topology BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma gaussian_linear_moment_eq_zero (p : V [×1]→L[ℝ] ℝ) {Q : V → ℝ}
    (hQ : ∀ x, Q (-x) = Q x) :
    (∫ x : V, p (fun _ ↦ x) * Real.exp (-Q x)) = 0 := by
  have hp (x : V) : p (fun _ ↦ -x) = -p (fun _ ↦ x) := by
    simpa only [neg_one_smul, pow_one, neg_one_mul] using
      multilinear_diagonal_homogeneous p (-1) x
  have he := Measure.integral_comp_smul (volume : Measure V)
    (fun x ↦ p (fun _ ↦ x) * Real.exp (-Q x)) (-1 : ℝ)
  simp only [neg_one_smul, hp, hQ, neg_mul, integral_neg,
    abs_inv, abs_pow, abs_neg, abs_one, one_pow, inv_one, one_smul] at he
  linarith

theorem analytic_gaussian_amplitude_leading_term {K L : Set V}
    (hK : MeasurableSet K) (hL : IsCompact L) (hKL : K ⊆ L)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) (hball : Metric.ball 0 ε ⊆ K)
    {h Q : V → ℝ} (hh : ContinuousOn h L) (hha : AnalyticAt ℝ h 0)
    (hQc : Continuous Q) (hQb : ∀ x, b * ‖x‖ ^ 2 ≤ Q x)
    (hQs : ∀ (t : ℝ), 0 < t → ∀ x, Q (t • x) = t ^ 2 * Q x)
    (hQeven : ∀ x, Q (-x) = Q x) :
    (fun n : ℕ ↦ (∫ x in K, h x * Real.exp (-(n : ℝ) * Q x)) -
      (n : ℝ) ^ (-(Module.finrank ℝ V : ℝ) / 2) * h 0 * ∫ x : V, Real.exp (-Q x))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-(Module.finrank ℝ V : ℝ) / 2 - 1)) := by
  obtain ⟨p, hp⟩ := hha
  have he := analytic_gaussian_amplitude_expansion hK hL hKL hε hb hball hh hp hQc hQb hQs 2
  have hc0 : gaussianAmplitudeCoefficient p Q 0 = h 0 * ∫ x : V, Real.exp (-Q x) := by
    unfold gaussianAmplitudeCoefficient
    simp_rw [hp.coeff_zero]
    exact integral_const_mul _ _
  have hc1 : gaussianAmplitudeCoefficient p Q 1 = 0 := gaussian_linear_moment_eq_zero (p 1) hQeven
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hc0, hc1,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_zero, add_zero] at he
  have hexp : -((Module.finrank ℝ V : ℝ) + 2) / 2 = -(Module.finrank ℝ V : ℝ) / 2 - 1 := by ring
  simpa only [hexp, mul_assoc] using he

/-- The leading term of an analytic powered integral is its Gaussian volume. -/
theorem analytic_power_integral_leading_term {K L : Set V}
    (hK : MeasurableSet K) (hL : IsCompact L) (hKL : K ⊆ L)
    {ε b C H : ℝ} (hε : 0 < ε) (hb : 0 < b) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hball : Metric.ball 0 ε ⊆ K) {ψ Q h : V → ℝ}
    (hψc : ContinuousOn ψ L) (hQc : Continuous Q) (hhc : ContinuousOn h L)
    (hha : AnalyticAt ℝ h 0)
    (hQb : ∀ x, b * ‖x‖ ^ 2 ≤ Q x)
    (hQs : ∀ (t : ℝ), 0 < t → ∀ x, Q (t • x) = t ^ 2 * Q x)
    (hQeven : ∀ x, Q (-x) = Q x)
    (hψ0 : ∀ x ∈ K, 0 ≤ ψ x)
    (hψ : ∀ x ∈ K, ψ x ≤ Real.exp (-b * ‖x‖ ^ 2))
    (hδ : ∀ x ∈ K, |ψ x - Real.exp (-Q x)| ≤ C * ‖x‖ ^ 4)
    (hh : ∀ x ∈ K, |h x| ≤ H) :
    (fun n : ℕ ↦ (∫ x in K, h x * ψ x ^ n) -
      (n : ℝ) ^ (-(Module.finrank ℝ V : ℝ) / 2) * h 0 * ∫ x : V, Real.exp (-Q x))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-(Module.finrank ℝ V : ℝ) / 2 - 1)) := by
  have hpow := powered_integral_gaussian_approximation hK hL hKL hψc hQc.continuousOn hhc
    hb hC hH 1 (by omega) hψ0 hψ (fun x _ ↦ hQb x) hδ hh
  simp only [Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_mul,
    poweredGaussianAmplitude, Nat.cast_zero, zero_mul, Real.exp_zero, mul_one, pow_zero] at hpow
  have hgauss := analytic_gaussian_amplitude_leading_term hK hL hKL hε hb hball hhc hha
    hQc hQb hQs hQeven
  simpa only [sub_add_sub_cancel] using hpow.add hgauss

end OdlyzkoPoonen
