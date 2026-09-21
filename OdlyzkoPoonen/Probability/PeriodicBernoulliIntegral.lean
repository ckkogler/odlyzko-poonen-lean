import OdlyzkoPoonen.Analysis.FiniteCharacterAmplitude
import OdlyzkoPoonen.Analysis.UnitFourierCube
import OdlyzkoPoonen.Probability.BernoulliFourierProduct
import OdlyzkoPoonen.Combinatorics.PeriodicProducts

/-!
# Periodic Bernoulli sums as powered cosine integrals

Two complete zero-sum periods give a nonnegative cosine product. The remaining
finite block contributes a fixed analytic amplitude, independently of the
number of complete periods.
-/

namespace OdlyzkoPoonen
noncomputable section
open MeasureTheory UnitAddTorus
open scoped BigOperators Classical

local instance periodicBernoulliMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance periodicBernoulliHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance periodicBernoulliProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d ι : Type*} [Fintype d] [Fintype ι]

lemma uniformAverage_bit_characters_normalized (a : d → ℤ) (v : ι → d → ℤ)
    (t : UnitAddTorus d) :
    uniformAverage (fun w : ι → Bool ↦ (mFourier (a + ∑ i, bitValue (w i) • v i) t).re) =
      (mFourier a t * ∏ i, ((1 + mFourier (v i) t) / 2)).re := by
  rw [uniformAverage_bit_integer_characters]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, ← mul_div_assoc]
  rw [show (2 : ℂ) ^ Fintype.card ι = ((2 : ℝ) ^ Fintype.card ι : ℝ) by norm_cast,
    Complex.div_ofReal_re]

lemma finiteCharacterAmplitude_bit_product (a : d → ℤ) (v : ι → d → ℤ)
    (x : EuclideanSpace ℝ d) :
    finiteCharacterAmplitude (fun w : ι → Bool ↦ a + ∑ i, bitValue (w i) • v i) x =
      (mFourier a (fun j ↦ (x j : UnitAddCircle)) *
        ∏ i, ((1 + mFourier (v i) (fun j ↦ (x j : UnitAddCircle))) / 2)).re := by
  rw [finiteCharacterAmplitude_eq_character_average]
  convert uniformAverage_bit_characters_normalized a v (fun j ↦ (x j : UnitAddCircle)) using 1

omit [Fintype ι] in
lemma periodic_bit_product (v : ℕ → d → ℤ) {q : ℕ} (hq : 0 < q)
    (hv : ∀ j, v (j + q) = v j) (hz : ∑ j : Fin q, v j.val = 0)
    (k r : ℕ) (x : EuclideanSpace ℝ d) :
    (∏ i : Fin (2 * q * k + r),
      (1 + mFourier (v (i.val + 1)) (fun j ↦ (x j : UnitAddCircle))) / 2) =
      (cosineSquareProduct (fun i : Fin q ↦ Real.pi • integerLinearForm (v i.val)) x : ℂ) ^ k *
        ∏ i : Fin r, (1 + mFourier (v (i.val + 1)) (fun j ↦ (x j : UnitAddCircle))) / 2 := by
  let g : ℕ → ℂ := fun i ↦ (1 + mFourier (v i) (fun j ↦ (x j : UnitAddCircle))) / 2
  have hg : ∀ j, g (j + q) = g j := by intro j; simp only [g, hv j]
  have hg2 : ∀ j, g (j + 2 * q) = g j := by
    intro j
    rw [show j + 2 * q = (j + q) + q by omega, hg, hg]
  have hprod : (∏ j ∈ Finset.range (2 * q), g j) =
      (cosineSquareProduct (fun i : Fin q ↦ Real.pi • integerLinearForm (v i.val)) x : ℂ) := by
    have he := periodic_prod_blocks g q hg 2 0
    simp only [Nat.add_zero, Finset.range_zero, Finset.prod_empty, mul_one] at he
    rw [Nat.mul_comm q 2] at he
    rw [he, ← Fin.prod_univ_eq_prod_range]
    exact squared_period_character_eq_cosineSquareProduct (fun i : Fin q ↦ v i.val) hz x
  change (∏ j : Fin (2 * q * k + r), g (j.val + 1)) =
    _ * ∏ j : Fin r, g (j.val + 1)
  rw [Fin.prod_univ_eq_prod_range (fun j ↦ g (j + 1)),
    Fin.prod_univ_eq_prod_range (fun j ↦ g (j + 1))]
  rw [periodic_prod_blocks_shift g (by omega : 0 < 2 * q) hg2, hprod]

omit [Fintype ι] in
/-- Exact formula for every block count, including zero. -/
theorem uniformProbability_periodic_bit_vector_zero (a : d → ℤ) (v : ℕ → d → ℤ)
    {q : ℕ} (hq : 0 < q) (hv : ∀ j, v (j + q) = v j)
    (hz : ∑ j : Fin q, v j.val = 0) (k r : ℕ) :
    uniformProbability (fun w : Fin (2 * q * k + r) → Bool ↦
      a + ∑ i, bitValue (w i) • v (i.val + 1) = 0) =
      ∫ x in unitFourierCube d,
        finiteCharacterAmplitude (fun w : Fin r → Bool ↦
          a + ∑ i, bitValue (w i) • v (i.val + 1)) x *
        cosineSquareProduct (fun i : Fin q ↦ Real.pi • integerLinearForm (v i.val)) x ^ k := by
  have hf := uniformProbability_bit_vector_zero_fourier a
    (fun i : Fin (2 * q * k + r) ↦ v (i.val + 1))
  rw [torus_integral_eq_unitFourierCube] at hf
  calc
    _ = ∫ x in unitFourierCube d,
        (mFourier a (fun i ↦ (x i : UnitAddCircle)) *
          ∏ i : Fin (2 * q * k + r),
            (1 + mFourier (v (i.val + 1)) (fun j ↦ (x j : UnitAddCircle)))).re /
          (2 : ℝ) ^ Fintype.card (Fin (2 * q * k + r)) := by
      convert hf using 1
      exact congrArg (fun inst : Fintype (Fin (2 * q * k + r) → Bool) ↦
        @uniformProbability (Fin (2 * q * k + r) → Bool) inst (fun w ↦
          a + ∑ i, bitValue (w i) • v (i.val + 1) = 0)) (Subsingleton.elim _ _)
    _ = _ := ?_
  apply setIntegral_congr_fun (unitFourierCube_measurable d)
  intro x _
  dsimp only
  have hnorm := uniformAverage_bit_characters_normalized a
    (fun i : Fin (2 * q * k + r) ↦ v (i.val + 1))
    (fun i ↦ (x i : UnitAddCircle))
  rw [uniformAverage_bit_integer_characters] at hnorm
  have ham : finiteCharacterAmplitude (fun w : Fin r → Bool ↦
        a + ∑ i, bitValue (w i) • v (i.val + 1)) x =
      (mFourier a (fun j ↦ (x j : UnitAddCircle)) *
        ∏ i : Fin r, ((1 + mFourier (v (i.val + 1))
          (fun j ↦ (x j : UnitAddCircle))) / 2)).re := by
    convert finiteCharacterAmplitude_bit_product a (fun i : Fin r ↦ v (i.val + 1)) x using 1
    exact congrArg (fun inst : Fintype (Fin r → Bool) ↦
      @finiteCharacterAmplitude d (Fin r → Bool) _ inst
        (fun w ↦ a + ∑ i, bitValue (w i) • v (i.val + 1)) x) (Subsingleton.elim _ _)
  rw [hnorm, periodic_bit_product v hq hv hz k r x, ham]
  rw [← Complex.ofReal_pow]
  have he (A B : ℂ) (c : ℝ) : (A * ((c : ℂ) * B)).re = (A * B).re * c := by
    rw [show A * ((c : ℂ) * B) = (A * B) * (c : ℂ) by ring, Complex.mul_re]
    simp
  exact he _ _ _

end
end OdlyzkoPoonen
