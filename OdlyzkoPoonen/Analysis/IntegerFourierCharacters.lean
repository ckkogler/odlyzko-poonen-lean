import OdlyzkoPoonen.Probability.FiniteFourierInversion
import OdlyzkoPoonen.Analysis.CosineProductExpansion
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Integer Fourier characters in real coordinates

Canonical lattice characters are exponentials of real linear forms. A zero-sum
period cancels the complex phase, and doubling that period gives a product
of nonnegative cosine squares.
-/

namespace OdlyzkoPoonen
noncomputable section
open UnitAddTorus
open scoped BigOperators Classical

variable {d ι : Type*} [Fintype d] [Fintype ι]

/-- The real linear form associated to an integer lattice vector. -/
def integerLinearForm (v : d → ℤ) : EuclideanSpace ℝ d →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ ∑ i, (v i : ℝ) * x i
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.mul_sum, mul_left_comm] }

lemma integerLinearForm_apply (v : d → ℤ) (x : EuclideanSpace ℝ d) :
    integerLinearForm v x = ∑ i, (v i : ℝ) * x i := rfl

lemma integerLinearForm_sum_zero (v : ι → d → ℤ) (hv : ∑ i, v i = 0)
    (x : EuclideanSpace ℝ d) : ∑ i, integerLinearForm (v i) x = 0 := by
  simp_rw [integerLinearForm_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Finset.sum_mul, ← Int.cast_sum]
  have hj := congrFun hv j
  simp only [Finset.sum_apply, Pi.zero_apply] at hj
  rw [hj, Int.cast_zero, zero_mul]

lemma integer_character_real_coordinates (v : d → ℤ) (x : EuclideanSpace ℝ d) :
    mFourier v (fun i ↦ (x i : UnitAddCircle)) =
      Complex.exp (((2 * Real.pi * integerLinearForm v x : ℝ) : ℂ) * Complex.I) := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  simp only [integerLinearForm_apply, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_sum, Complex.ofReal_intCast, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype d] [Fintype ι] in
lemma fair_bit_exponential_eq_cosine (x : ℝ) :
    (1 + Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)) / 2 =
      Complex.exp ((x : ℂ) * Complex.I) * (Real.cos x : ℂ) := by
  have hcos : (Real.cos x : ℂ) =
      (Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (-(x : ℂ) * Complex.I)) / 2 := by
    rw [Complex.ofReal_cos, ← Complex.two_cos]
    ring
  rw [hcos, ← mul_div_assoc, mul_add, ← Complex.exp_add, ← Complex.exp_add]
  have hz : (x : ℂ) * Complex.I + -(x : ℂ) * Complex.I = 0 := by ring
  rw [hz, Complex.exp_zero]
  congr 1
  push_cast
  rw [add_comm (1 : ℂ)]
  congr 1
  ring

omit [Fintype d] in
lemma prod_fair_bit_exponential_zero_sum (a : ι → ℝ) (ha : ∑ i, a i = 0) :
    (∏ i, (1 + Complex.exp (((2 * a i : ℝ) : ℂ) * Complex.I)) / 2) =
      ((∏ i, Real.cos (a i) : ℝ) : ℂ) := by
  simp_rw [fair_bit_exponential_eq_cosine]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.sum_mul, ← Complex.ofReal_sum,
    ha, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, Complex.ofReal_prod]

lemma squared_period_character_eq_cosineSquareProduct (v : ι → d → ℤ)
    (hv : ∑ i, v i = 0) (x : EuclideanSpace ℝ d) :
    (∏ i, (1 + mFourier (v i) (fun j ↦ (x j : UnitAddCircle))) / 2) ^ 2 =
      (cosineSquareProduct (fun i ↦ Real.pi • integerLinearForm (v i)) x : ℂ) := by
  have ha : ∑ i, Real.pi * integerLinearForm (v i) x = 0 := by
    rw [← Finset.mul_sum, integerLinearForm_sum_zero v hv x, mul_zero]
  simp_rw [integer_character_real_coordinates]
  have hre (i : ι) : 2 * Real.pi * integerLinearForm (v i) x =
      2 * (Real.pi * integerLinearForm (v i) x) := by ring
  simp_rw [hre]
  rw [prod_fair_bit_exponential_zero_sum _ ha, ← Complex.ofReal_pow]
  congr 1
  simp only [cosineSquareProduct, smul_apply, smul_eq_mul,
    Finset.prod_pow]

end
end OdlyzkoPoonen
