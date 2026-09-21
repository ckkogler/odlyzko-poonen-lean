import OdlyzkoPoonen.Analysis.GaussianAmplitudeExpansion
import OdlyzkoPoonen.Analysis.PoweredGaussianApproximation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Fixed amplitudes in a powered Gaussian expansion

Moving the finite powers of the base Gaussian into the amplitudes leaves
one common concentrating Gaussian. The amplitudes are independent of the
large integer parameter and retain their analytic vanishing orders.
-/

namespace OdlyzkoPoonen
open MeasureTheory Filter Asymptotics
open scoped Topology BigOperators

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def poweredGaussianAmplitude (ψ Q h : V → ℝ) (r : ℕ) (x : V) : ℝ :=
  h x * Real.exp ((r : ℝ) * Q x) * (ψ x - Real.exp (-Q x)) ^ r

omit [NormedSpace ℝ V] in
lemma poweredGaussianAmplitude_continuousOn {K : Set V} {ψ Q h : V → ℝ}
    (hψ : ContinuousOn ψ K) (hQ : ContinuousOn Q K) (hh : ContinuousOn h K) (r : ℕ) :
    ContinuousOn (poweredGaussianAmplitude ψ Q h r) K := by
  unfold poweredGaussianAmplitude
  fun_prop

lemma poweredGaussianAmplitude_analyticAt {ψ Q h : V → ℝ}
    (hψ : AnalyticAt ℝ ψ 0) (hQ : AnalyticAt ℝ Q 0) (hh : AnalyticAt ℝ h 0) (r : ℕ) :
    AnalyticAt ℝ (poweredGaussianAmplitude ψ Q h r) 0 := by
  have he (x : ℝ) : AnalyticAt ℝ Real.exp x := Real.contDiff_exp.contDiffAt.analyticAt
  exact (hh.mul ((he _).comp (analyticAt_const.mul hQ))).mul
    ((hψ.sub ((he _).comp hQ.neg)).pow r)

omit [NormedSpace ℝ V] in
lemma poweredGaussianAmplitude_vanishing {ψ Q h : V → ℝ}
    (hQ : ContinuousAt Q 0) (hh : ContinuousAt h 0)
    (hδ : (fun x ↦ ψ x - Real.exp (-Q x)) =O[𝓝 0] (fun x : V ↦ ‖x‖ ^ 4)) (r : ℕ) :
    poweredGaussianAmplitude ψ Q h r =O[𝓝 0] (fun x : V ↦ ‖x‖ ^ (4 * r)) := by
  have ha : ContinuousAt (fun x ↦ h x * Real.exp ((r : ℝ) * Q x)) 0 := by fun_prop
  have hab : (fun x ↦ h x * Real.exp ((r : ℝ) * Q x)) =O[𝓝 0] (fun _ : V ↦ (1 : ℝ)) :=
    ha.isBigO_one ℝ
  simpa only [poweredGaussianAmplitude, one_mul, ← pow_mul] using! hab.mul (hδ.pow r)

lemma poweredGaussianAmplitude_low_coefficient {ψ Q h : V → ℝ}
    (hQ : ContinuousAt Q 0) (hh : ContinuousAt h 0)
    (hδ : (fun x ↦ ψ x - Real.exp (-Q x)) =O[𝓝 0] (fun x : V ↦ ‖x‖ ^ 4))
    (r : ℕ) {p : FormalMultilinearSeries ℝ V ℝ}
    (hp : HasFPowerSeriesAt (poweredGaussianAmplitude ψ Q h r) p 0)
    (j : ℕ) (hj : j < 4 * r) (x : V) : p j (fun _ ↦ x) = 0 :=
  analytic_homogeneous_term_eq_zero_of_isBigO hp
    (poweredGaussianAmplitude_vanishing hQ hh hδ r) j hj x

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma truncatedPowerExpansion_gaussian_amplitudes {ψ Q h : V → ℝ}
    (n R : ℕ) (hR : R ≤ n + 1) (x : V) :
    h x * truncatedPowerExpansion n R (ψ x) (Real.exp (-Q x)) =
      ∑ r ∈ Finset.range R, (n.choose r : ℝ) *
        (poweredGaussianAmplitude ψ Q h r x * Real.exp (-(n : ℝ) * Q x)) := by
  unfold truncatedPowerExpansion
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrn : r ≤ n := by have := Finset.mem_range.mp hr; omega
  have he : Real.exp (-Q x) ^ (n - r) =
      Real.exp ((r : ℝ) * Q x) * Real.exp (-(n : ℝ) * Q x) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_sub hrn]
    congr 1
    ring
  rw [he]
  unfold poweredGaussianAmplitude
  ring

end OdlyzkoPoonen
