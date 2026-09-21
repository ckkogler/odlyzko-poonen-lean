import OdlyzkoPoonen.Analysis.IntegerFourierCharacters
import OdlyzkoPoonen.Probability.AverageBounds

/-!
# Analytic amplitudes from finite integer offsets

A finite average of integer characters is a real analytic, even amplitude.
It is bounded by one and equals one at the origin for every nonempty finite
sample space, including any fixed residual block of fair bits.
-/

namespace OdlyzkoPoonen
noncomputable section
open UnitAddTorus
open scoped BigOperators

variable {d α : Type*} [Fintype d] [Fintype α]

def finiteCharacterAmplitude (S : α → d → ℤ) (x : EuclideanSpace ℝ d) : ℝ :=
  uniformAverage (fun a ↦ Real.cos (2 * Real.pi * integerLinearForm (S a) x))

lemma finiteCharacterAmplitude_continuous (S : α → d → ℤ) :
    Continuous (finiteCharacterAmplitude S) := by
  unfold finiteCharacterAmplitude uniformAverage
  fun_prop

lemma finiteCharacterAmplitude_analyticAt (S : α → d → ℤ) (x : EuclideanSpace ℝ d) :
    AnalyticAt ℝ (finiteCharacterAmplitude S) x := by
  unfold finiteCharacterAmplitude uniformAverage
  simp only [div_eq_mul_inv]
  apply AnalyticAt.mul _ analyticAt_const
  apply Finset.analyticAt_fun_sum
  intro a _
  exact Real.analyticAt_cos.comp (analyticAt_const.mul ((integerLinearForm (S a)).analyticAt x))

lemma finiteCharacterAmplitude_zero [Nonempty α] (S : α → d → ℤ) :
    finiteCharacterAmplitude S 0 = 1 := by
  simp [finiteCharacterAmplitude, uniformAverage_const]

lemma finiteCharacterAmplitude_abs_le_one [Nonempty α] (S : α → d → ℤ)
    (x : EuclideanSpace ℝ d) : |finiteCharacterAmplitude S x| ≤ 1 := by
  apply abs_le.mpr
  constructor
  · calc
      _ = uniformAverage (fun _ : α ↦ (-1 : ℝ)) := (uniformAverage_const (-1)).symm
      _ ≤ _ := uniformAverage_mono (fun _ ↦ Real.neg_one_le_cos _)
  · calc
      _ ≤ uniformAverage (fun _ : α ↦ (1 : ℝ)) := uniformAverage_mono (fun _ ↦ Real.cos_le_one _)
      _ = _ := uniformAverage_const 1

lemma finiteCharacterAmplitude_even (S : α → d → ℤ) (x : EuclideanSpace ℝ d) :
    finiteCharacterAmplitude S (-x) = finiteCharacterAmplitude S x := by
  simp [finiteCharacterAmplitude, mul_neg]

lemma finiteCharacterAmplitude_eq_character_average (S : α → d → ℤ) (x : EuclideanSpace ℝ d) :
    finiteCharacterAmplitude S x =
      uniformAverage (fun a ↦ (mFourier (S a) (fun i ↦ (x i : UnitAddCircle))).re) := by
  simp only [integer_character_real_coordinates, Complex.exp_ofReal_mul_I_re]
  rfl

end
end OdlyzkoPoonen
