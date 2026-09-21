import OdlyzkoPoonen.Probability.UniformAverage
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Fourier inversion for finite integer-valued statistics

Character orthogonality expresses the exact probability of a zero integer
vector as an integral over the unit torus. No limiting probability theorem
is used in this identity.
-/

namespace OdlyzkoPoonen
noncomputable section
open MeasureTheory UnitAddTorus
open scoped BigOperators Classical

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d α : Type*} [Fintype d] [Fintype α]

lemma integral_integer_character (v : d → ℤ) :
    (∫ t : UnitAddTorus d, mFourier v t) = if v = 0 then (1 : ℂ) else 0 := by
  have h := orthonormal_iff_ite.mp (orthonormal_mFourier (d := d)) (0 : d → ℤ) v
  simpa only [ContinuousMap.inner_toLp, ← mFourier_neg, ← mFourier_add,
    neg_zero, zero_add, add_zero, eq_comm] using h

lemma integrable_integer_character (v : d → ℤ) :
    Integrable (fun t : UnitAddTorus d ↦ mFourier v t) := by
  simpa only [integrableOn_univ] using
    (mFourier v).continuous.continuousOn.integrableOn_compact isCompact_univ

lemma integral_re_integer_character (v : d → ℤ) :
    (∫ t : UnitAddTorus d, (mFourier v t).re) = if v = 0 then (1 : ℝ) else 0 := by
  have he := integral_re (integrable_integer_character v)
  rw [integral_integer_character] at he
  simpa only [RCLike.re_to_complex, apply_ite, Complex.one_re, Complex.zero_re] using he

/-- Finite Fourier inversion on the full integer lattice. -/
theorem uniformProbability_zero_eq_torus_integral (S : α → d → ℤ) :
    uniformProbability (fun a ↦ S a = 0) =
      ∫ t : UnitAddTorus d, uniformAverage (fun a ↦ (mFourier (S a) t).re) := by
  rw [uniformProbability_eq_average_indicator]
  unfold uniformAverage
  rw [integral_div, integral_finsetSum]
  · simp_rw [integral_re_integer_character]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : S a = 0 <;> simp [ha]
  · intro a _
    exact (integrable_integer_character (S a)).re

end
end OdlyzkoPoonen
