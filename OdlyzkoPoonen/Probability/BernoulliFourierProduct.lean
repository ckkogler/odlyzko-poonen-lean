import OdlyzkoPoonen.Probability.FiniteFourierInversion
import OdlyzkoPoonen.Probability.BinaryModel
import OdlyzkoPoonen.Probability.FiniteBitSums
import OdlyzkoPoonen.Polynomial.RemainderCoordinates

/-!
# Exact Fourier products for independent fair bits

The finite sum over all words factors into one term per bit. Applied to monic
remainder coordinates, this is an exact integral formula for divisibility.
-/

namespace OdlyzkoPoonen
noncomputable section
open MeasureTheory UnitAddTorus
open scoped BigOperators Classical

local instance bernoulliFourierMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance bernoulliFourierHaarMeasure : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance bernoulliFourierProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d ι : Type*} [Fintype d] [Fintype ι]

omit [Fintype ι] in
lemma integer_character_sum (s : Finset ι) (v : ι → d → ℤ) (t : UnitAddTorus d) :
    mFourier (∑ i ∈ s, v i) t = ∏ i ∈ s, mFourier (v i) t := by
  induction s using Finset.induction_on with
  | empty => simp [mFourier_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, mFourier_add, ih]

lemma sum_bit_integer_characters (a : d → ℤ) (v : ι → d → ℤ) (t : UnitAddTorus d) :
    (∑ w : ι → Bool, mFourier (a + ∑ i, bitValue (w i) • v i) t) =
      mFourier a t * ∏ i, (1 + mFourier (v i) t) := by
  simp_rw [mFourier_add, integer_character_sum]
  rw [← Finset.mul_sum, ← Fintype.prod_sum
    (fun (i : ι) (b : Bool) ↦ mFourier (bitValue b • v i) t)]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp [bitValue, mFourier_zero, add_comm]

lemma uniformAverage_bit_integer_characters (a : d → ℤ) (v : ι → d → ℤ)
    (t : UnitAddTorus d) :
    uniformAverage (fun w : ι → Bool ↦ (mFourier (a + ∑ i, bitValue (w i) • v i) t).re) =
      (mFourier a t * ∏ i, (1 + mFourier (v i) t)).re / (2 : ℝ) ^ Fintype.card ι := by
  unfold uniformAverage
  have he := congrArg Complex.re (sum_bit_integer_characters a v t)
  simp only [Complex.re_sum] at he
  rw [he]
  simp

/-- Exact Fourier inversion followed by finite Bernoulli factorization. -/
theorem uniformProbability_bit_vector_zero_fourier (a : d → ℤ) (v : ι → d → ℤ) :
    uniformProbability (fun w : ι → Bool ↦ a + ∑ i, bitValue (w i) • v i = 0) =
      ∫ t : UnitAddTorus d,
        (mFourier a t * ∏ i, (1 + mFourier (v i) t)).re / (2 : ℝ) ^ Fintype.card ι := by
  rw [uniformProbability_zero_eq_torus_integral]
  simp_rw [uniformAverage_bit_integer_characters]

/-- The finite binary polynomial model expressed in canonical integer coordinates. -/
theorem binaryProbability_monic_divisor_fourier (m : ℕ) {f : Polynomial ℤ} (hf : f.Monic) :
    binaryProbability m (fun p ↦ f ∣ p) =
      ∫ t : UnitAddTorus (Fin f.natDegree),
        (mFourier (powerRemainderCoordinates f 0 + powerRemainderCoordinates f (m + 1)) t *
          ∏ i : Fin m, (1 + mFourier (powerRemainderCoordinates f (i.val + 1)) t)).re /
          (2 : ℝ) ^ m := by
  unfold binaryProbability
  have he : (fun w : Fin m → Bool ↦ f ∣ wordPolynomial w) =
      (fun w : Fin m → Bool ↦
        (powerRemainderCoordinates f 0 + powerRemainderCoordinates f (m + 1)) +
          ∑ i, bitValue (w i) • powerRemainderCoordinates f (i.val + 1) = 0) := by
    funext w
    apply propext
    rw [dvd_wordPolynomial_iff_remainderCoordinates_eq_zero hf]
    simp only [add_assoc, add_left_comm, add_comm]
  rw [he]
  have hfourier := uniformProbability_bit_vector_zero_fourier
    (powerRemainderCoordinates f 0 + powerRemainderCoordinates f (m + 1))
    (fun i : Fin m ↦ powerRemainderCoordinates f (i.val + 1))
  simp only [Fintype.card_fin] at hfourier
  convert hfourier using 1
  exact congrArg (fun inst : Fintype (Fin m → Bool) ↦
    @uniformProbability (Fin m → Bool) inst (fun w ↦
      powerRemainderCoordinates f 0 + powerRemainderCoordinates f (m + 1) +
        ∑ i, bitValue (w i) • powerRemainderCoordinates f (i.val + 1) = 0))
    (Subsingleton.elim _ _)

end
end OdlyzkoPoonen
