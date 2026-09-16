import OdlyzkoPoonen.Polynomial.DivisorCoefficientBound
import Mathlib.Data.Int.Interval

/-!
# Finite families covering bounded monic polynomials

A monic degree-`h` polynomial is determined by its `h` lower coefficients.
Choosing each coefficient from the integer interval `[-H,H]` gives a finite
candidate family of size at most `(2*H+1)^h`. The leading coefficient is fixed
at one. Every monic divisor with the proved coefficient bound belongs to the
corresponding family, including degree zero when needed.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

/-- A polynomial with a prescribed leading one and the given lower coefficients. -/
noncomputable def monicPolynomialOfCoefficients {h : ℕ} (w : Fin h → ℤ) : ℤ[X] :=
  X ^ h + ∑ i : Fin h, C (w i) * X ^ i.val

lemma monic_eq_polynomialOfCoefficients {p : ℤ[X]} (hp : p.Monic) :
    p = monicPolynomialOfCoefficients (fun i : Fin p.natDegree ↦ p.coeff i.val) := by
  unfold monicPolynomialOfCoefficients
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ C (p.coeff i) * X ^ i) p.natDegree]
  calc
    p = ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^ i :=
      p.as_sum_range_C_mul_X_pow
    _ = _ := by rw [Finset.sum_range_succ, hp.coeff_natDegree, C_1, one_mul, add_comm]

/-- The finite pool obtained by choosing bounded lower integer coefficients. -/
noncomputable def boundedMonicFamily (h H : ℕ) : Finset ℤ[X] :=
  Finset.univ.image (fun w : Fin h → {z : ℤ // z ∈ Finset.Icc (-(H : ℤ)) H} ↦
    monicPolynomialOfCoefficients (fun i ↦ (w i).val))

lemma card_bounded_integer_interval (H : ℕ) :
    (Finset.Icc (-(H : ℤ)) H).card = 2 * H + 1 := by
  rw [Int.card_Icc]
  omega

lemma card_boundedMonicFamily_le (h H : ℕ) :
    (boundedMonicFamily h H).card ≤ (2 * H + 1) ^ h := by
  unfold boundedMonicFamily
  calc
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = _ := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe,
        card_bounded_integer_interval, Fintype.card_fin]

lemma mem_boundedMonicFamily_of_coeff_bound {h H : ℕ} {p : ℤ[X]}
    (hp : p.Monic) (hdeg : p.natDegree = h) (hc : ∀ k < h, |p.coeff k| ≤ (H : ℤ)) :
    p ∈ boundedMonicFamily h H := by
  let w : Fin h → {z : ℤ // z ∈ Finset.Icc (-(H : ℤ)) H} := fun i ↦
    ⟨p.coeff i.val, Finset.mem_Icc.mpr (abs_le.mp (hc i.val i.isLt))⟩
  apply Finset.mem_image.mpr
  refine ⟨w, Finset.mem_univ _, ?_⟩
  have he := monic_eq_polynomialOfCoefficients hp
  rw [hdeg] at he
  exact he.symm

lemma HasBinaryEndpoints.monic_divisor_mem_boundedFamily {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p) :
    J ∈ boundedMonicFamily J.natDegree (3 ^ J.natDegree) := by
  apply mem_boundedMonicFamily_of_coeff_bound hJ rfl
  intro k _
  exact_mod_cast hp.monic_divisor_coeff_abs_le hJ hdvd k

end OdlyzkoPoonen
