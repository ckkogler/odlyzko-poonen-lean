import OdlyzkoPoonen.Analysis.PoweredGaussianAmplitudes
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Finite-order integral expansions of large analytic powers

The binomial perturbation and the homogeneous Gaussian amplitude expansion
combine with a uniform remainder. All coefficients are fixed Gaussian moments;
the only remaining dependence on the large integer is explicit.
-/

namespace OdlyzkoPoonen
open MeasureTheory Filter Asymptotics
open scoped Topology BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem powered_integral_gaussian_approximation {K L : Set V}
    (hK : MeasurableSet K) (hL : IsCompact L) (hKL : K ⊆ L)
    {ψ Q h : V → ℝ} (hψc : ContinuousOn ψ L) (hQc : ContinuousOn Q L)
    (hhc : ContinuousOn h L) {b C H : ℝ} (hb : 0 < b) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (R : ℕ) (hR : 1 ≤ R)
    (hψ0 : ∀ x ∈ K, 0 ≤ ψ x)
    (hψ : ∀ x ∈ K, ψ x ≤ Real.exp (-b * ‖x‖ ^ 2))
    (hQ : ∀ x ∈ K, b * ‖x‖ ^ 2 ≤ Q x)
    (hδ : ∀ x ∈ K, |ψ x - Real.exp (-Q x)| ≤ C * ‖x‖ ^ 4)
    (hh : ∀ x ∈ K, |h x| ≤ H) :
    (fun n : ℕ ↦ (∫ x in K, h x * ψ x ^ n) -
      ∑ r ∈ Finset.range R, (n.choose r : ℝ) *
        ∫ x in K, poweredGaussianAmplitude ψ Q h r x * Real.exp (-(n : ℝ) * Q x))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-(Module.finrank ℝ V : ℝ) / 2 - R)) := by
  have he := powered_gaussian_remainder_isBigO hK hb hC hH R hR hψ0 hψ hQ hδ hh
  apply he.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop R] with n hn
  have hi : IntegrableOn (fun x ↦ h x * ψ x ^ n) K :=
    ((hhc.mul (hψc.pow n)).integrableOn_compact hL).mono_set hKL
  have ht : IntegrableOn
      (fun x ↦ h x * truncatedPowerExpansion n R (ψ x) (Real.exp (-Q x))) K := by
    apply IntegrableOn.mono_set (t := L) _ hKL
    apply ContinuousOn.integrableOn_compact hL
    unfold truncatedPowerExpansion
    fun_prop
  simp_rw [mul_sub]
  rw [integral_sub hi ht]
  congr 1
  simp_rw [truncatedPowerExpansion_gaussian_amplitudes n R (by omega)]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro r _
    apply IntegrableOn.mono_set (t := L) _ hKL
    apply ContinuousOn.integrableOn_compact hL
    have ha := poweredGaussianAmplitude_continuousOn hψc hQc hhc r
    fun_prop

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] in
lemma nat_choose_isBigO_rpow (r : ℕ) :
    (fun n : ℕ ↦ (n.choose r : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (r : ℝ)) := by
  apply Asymptotics.IsBigO.of_norm_eventuallyLE
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_eq_abs, Real.rpow_natCast,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n.choose r))]
  exact_mod_cast Nat.choose_le_pow n r

/-- A finite moment formula with a remainder of arbitrary prescribed order. -/
theorem powered_integral_moment_expansion {K L : Set V}
    (hK : MeasurableSet K) (hL : IsCompact L) (hKL : K ⊆ L)
    {ε b C H : ℝ} (hε : 0 < ε) (hb : 0 < b) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hball : Metric.ball 0 ε ⊆ K) {ψ Q h : V → ℝ}
    (hψc : ContinuousOn ψ L) (hQc : Continuous Q) (hhc : ContinuousOn h L)
    (hQb : ∀ x, b * ‖x‖ ^ 2 ≤ Q x)
    (hQs : ∀ (t : ℝ), 0 < t → ∀ x, Q (t • x) = t ^ 2 * Q x)
    (hψ0 : ∀ x ∈ K, 0 ≤ ψ x)
    (hψ : ∀ x ∈ K, ψ x ≤ Real.exp (-b * ‖x‖ ^ 2))
    (hδ : ∀ x ∈ K, |ψ x - Real.exp (-Q x)| ≤ C * ‖x‖ ^ 4)
    (hh : ∀ x ∈ K, |h x| ≤ H) (R : ℕ) (hR : 1 ≤ R)
    (p : ℕ → FormalMultilinearSeries ℝ V ℝ)
    (hp : ∀ r < R, HasFPowerSeriesAt (poweredGaussianAmplitude ψ Q h r) (p r) 0) :
    (fun n : ℕ ↦ (∫ x in K, h x * ψ x ^ n) -
      ∑ r ∈ Finset.range R, (n.choose r : ℝ) *
        ∑ j ∈ Finset.range (4 * R),
          (n : ℝ) ^ (-((Module.finrank ℝ V : ℝ) + j) / 2) *
            gaussianAmplitudeCoefficient (p r) Q j) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(Module.finrank ℝ V : ℝ) / 2 - R)) := by
  have he := powered_integral_gaussian_approximation hK hL hKL hψc hQc.continuousOn hhc
    hb hC hH R hR hψ0 hψ (fun x _ ↦ hQb x) hδ hh
  have hr (r : ℕ) (hr : r ∈ Finset.range R) :=
    analytic_gaussian_amplitude_expansion hK hL hKL hε hb hball
      (poweredGaussianAmplitude_continuousOn hψc hQc.continuousOn hhc r)
      (hp r (Finset.mem_range.mp hr)) hQc hQb hQs (4 * R)
  have hs (r : ℕ) (hr' : r ∈ Finset.range R) :=
    Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (r : ℝ) (-((Module.finrank ℝ V : ℝ) + (4 * R : ℕ)) / 2)
      (-(Module.finrank ℝ V : ℝ) / 2 - R) (nat_choose_isBigO_rpow r) (hr r hr')
      (by
        have hrr : (r : ℝ) < R := by exact_mod_cast Finset.mem_range.mp hr'
        push_cast
        linarith)
  have hsum := Asymptotics.IsBigO.sum hs
  have hall := he.add hsum
  convert! hall using 1
  funext n
  simp only [Pi.mul_apply, Finset.sum_apply, mul_sub, Finset.sum_sub_distrib]
  ring

end OdlyzkoPoonen
