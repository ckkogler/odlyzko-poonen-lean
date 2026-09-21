import OdlyzkoPoonen.Probability.FiniteFourierInversion
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Euclidean coordinates for the normalized Fourier torus

The half-open unit cube represents normalized torus integration exactly.
Its compact closure and a fixed interior ball provide the domains required
by the Gaussian remainder estimates.
-/

namespace OdlyzkoPoonen
noncomputable section
open MeasureTheory Set

local instance unitCubeMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance unitCubeHaarMeasure : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance unitCubeProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (d : Type*) [Fintype d]

def unitFourierCube : Set (EuclideanSpace ℝ d) :=
  {x | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2)}

def closedUnitFourierCube : Set (EuclideanSpace ℝ d) :=
  {x | ∀ i, x i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)}

lemma unitFourierCube_measurable : MeasurableSet (unitFourierCube d) := by
  simp only [unitFourierCube, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_Ioc.preimage (PiLp.continuous_apply 2 (fun _ : d ↦ ℝ) i).measurable

omit [Fintype d] in
lemma closedUnitFourierCube_compact : IsCompact (closedUnitFourierCube d) := by
  have he : closedUnitFourierCube d =
      WithLp.toLp 2 '' Set.pi Set.univ (fun _ : d ↦ Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    ext x
    constructor
    · intro hx
      exact ⟨x.ofLp, fun i _ ↦ hx i, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact fun i ↦ hy i (Set.mem_univ _)
  rw [he]
  exact (isCompact_univ_pi (fun _ ↦ isCompact_Icc)).image (PiLp.continuous_toLp 2 _)

omit [Fintype d] in
lemma unitFourierCube_subset_closed : unitFourierCube d ⊆ closedUnitFourierCube d :=
  fun _ hx i ↦ ⟨(hx i).1.le, (hx i).2⟩

lemma ball_subset_unitFourierCube : Metric.ball (0 : EuclideanSpace ℝ d) (1 / 2) ⊆
    unitFourierCube d := by
  intro x hx i
  have hn : ‖x‖ < (1 / 2 : ℝ) := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hi : |x i| < (1 / 2 : ℝ) := (PiLp.norm_apply_le x i).trans_lt hn
  exact ⟨(abs_lt.mp hi).1, (abs_lt.mp hi).2.le⟩

omit [Fintype d] in
lemma abs_coordinate_le_half {x : EuclideanSpace ℝ d} (hx : x ∈ closedUnitFourierCube d)
    (i : d) : |x i| ≤ (1 / 2 : ℝ) := abs_le.mpr (hx i)

/-- The normalization is exactly Lebesgue measure on one unit cube. -/
theorem torus_integral_eq_unitFourierCube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UnitAddTorus d → E) :
    (∫ t : UnitAddTorus d, f t) =
      ∫ x in unitFourierCube d, f (fun i ↦ (x i : UnitAddCircle)) := by
  rw [UnitAddTorus.integral_preimage f (fun _ ↦ -(1 / 2 : ℝ))]
  have he := (PiLp.volume_preserving_ofLp d).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (d → ℝ)).symm.measurableEmbedding
    (fun x : d → ℝ ↦ f (fun i ↦ (x i : UnitAddCircle)))
    {x : d → ℝ | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2)}
  norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
  exact he.symm

end
end OdlyzkoPoonen
