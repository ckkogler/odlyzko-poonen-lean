import OdlyzkoPoonen.Polynomial.InitialCoefficient
import OdlyzkoPoonen.FiniteField.InteriorPolynomial
import OdlyzkoPoonen.Probability.BitWeights

/-!
# Triangular convolution of finite coefficient words

Multiplication by a polynomial whose constant coefficient is one induces a
triangular bijection on any finite prefix of coefficients. The proof uses the
actual product coefficients. Its exact half-weight average is `(3/4)^m`, with
no distribution hypothesis beyond the uniform input word.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

lemma f2ToBit_add (x y : ZMod 2) : f2ToBit (x + y) = Bool.xor (f2ToBit x) (f2ToBit y) := by
  apply bitF2Equiv.injective
  change bitToF2 (f2ToBit (x + y)) = bitToF2 (Bool.xor (f2ToBit x) (f2ToBit y))
  rw [bitToF2_f2ToBit, bitToF2_xor, bitToF2_f2ToBit, bitToF2_f2ToBit]

/-- The first `m` positive coefficients of the actual product, as a Boolean word. -/
noncomputable def coefficientConvolution {m : ℕ} (q : (ZMod 2)[X])
    (w : Fin m → Bool) (i : Fin m) : Bool :=
  f2ToBit ((q * f2InteriorPolynomial w).coeff (i.val + 1))

/-- The contribution of strictly earlier input coefficients in the product. -/
noncomputable def coefficientConvolutionCorrection {m : ℕ} (q : (ZMod 2)[X])
    (w : Fin m → Bool) (i : Fin m) : Bool :=
  f2ToBit (∑ k ∈ Finset.range (i.val + 1),
    (f2InteriorPolynomial w).coeff k * q.coeff (i.val + 1 - k))

lemma coefficientConvolutionCorrection_dependsOnEarlier {m : ℕ} (q : (ZMod 2)[X]) :
    DependsOnEarlier (@coefficientConvolutionCorrection m q) := by
  intro i v w h
  apply congrArg f2ToBit
  apply Finset.sum_congr rfl
  intro k hk
  rw [f2InteriorPolynomial_prefix h (Finset.mem_range.mp hk)]

lemma coefficientConvolution_eq_triangular {m : ℕ} {q : (ZMod 2)[X]}
    (hq : q.coeff 0 = 1) (w : Fin m → Bool) :
    coefficientConvolution q w = triangularBitMap (coefficientConvolutionCorrection q) w := by
  funext i
  unfold coefficientConvolution triangularBitMap coefficientConvolutionCorrection
  rw [coeff_mul_constant_one q _ hq, coeff_f2InteriorPolynomial, f2ToBit_add,
    f2ToBit_bitToF2]

lemma coefficientConvolution_bijective {m : ℕ} {q : (ZMod 2)[X]}
    (hq : q.coeff 0 = 1) : Function.Bijective (@coefficientConvolution m q) := by
  have heq : @coefficientConvolution m q = triangularBitMap (coefficientConvolutionCorrection q) :=
    funext (coefficientConvolution_eq_triangular hq)
  rw [heq]
  exact triangularBitMap_bijective (coefficientConvolutionCorrection_dependsOnEarlier q)

lemma uniformAverage_coefficientConvolution_half_weight {m : ℕ} {q : (ZMod 2)[X]}
    (hq : q.coeff 0 = 1) :
    uniformAverage (fun w : Fin m → Bool ↦
      (1 / 2 : ℝ) ^ trueBitCount (coefficientConvolution q w)) = (3 / 4 : ℝ) ^ m := by
  simp only [coefficientConvolution_eq_triangular hq]
  exact uniformAverage_triangular_half_weight (coefficientConvolutionCorrection_dependsOnEarlier q)

end OdlyzkoPoonen
