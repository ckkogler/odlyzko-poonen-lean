import OdlyzkoPoonen.Polynomial.TaylorRootProducts
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Order.Interval.Finset.Fin

/-!
# Confluent Vandermonde determinant by a Newton basis

For a finite sequence of nodes, the derivative order at each node is its number
of previous occurrences. The matrix contains the divided (Hasse) derivatives
of the monomials. Multiplying by the coefficient matrix of the monic Newton
polynomials makes it lower triangular. The coefficient matrix has determinant
one, yielding the product of all differences between unequal earlier nodes.
The argument works over every nontrivial commutative ring, in all characteristics.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

/-- The monic Newton polynomial formed from all earlier nodes. -/
def rootPrefixPolynomial {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) : R[X] := ∏ i ∈ Finset.Iio j, (X - C (x i))

/-- Number of earlier occurrences of the same node. -/
def rootPrefixMultiplicity {R : Type*} {n : ℕ} (x : Fin n → R) (i : Fin n) : ℕ :=
  ((Finset.Iio i).filter (fun j ↦ x j = x i)).card

/-- Each row evaluates the divided derivative of its occurrence order. -/
def confluentVandermonde {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j ↦ (j.val.choose (rootPrefixMultiplicity x i) : R) *
    x i ^ (j.val - rootPrefixMultiplicity x i)

lemma rootPrefixPolynomial_monic {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (j : Fin n) : (rootPrefixPolynomial x j).Monic := by
  exact monic_prod_of_monic _ _ (fun i _ ↦ monic_X_sub_C (x i))

lemma rootPrefixPolynomial_natDegree {R : Type*} [CommRing R] [Nontrivial R]
    {n : ℕ} (x : Fin n → R) (j : Fin n) : (rootPrefixPolynomial x j).natDegree = j.val := by
  rw [rootPrefixPolynomial, natDegree_finsetProd_X_sub_C_eq_card, Fin.card_Iio]

lemma rootPrefixMultiplicity_le {R : Type*} {n : ℕ} (x : Fin n → R) (i : Fin n) :
    rootPrefixMultiplicity x i ≤ i.val := by
  rw [rootPrefixMultiplicity, ← Fin.card_Iio i]
  exact Finset.card_filter_le _ _

lemma rootPrefixMultiplicity_lt_later_count {R : Type*} {n : ℕ}
    (x : Fin n → R) {i j : Fin n} (hij : i < j) :
    rootPrefixMultiplicity x i < ((Finset.Iio j).filter (fun k ↦ x k = x i)).card := by
  have hi : i ∉ (Finset.Iio i).filter (fun k ↦ x k = x i) := by simp
  have hsub : insert i ((Finset.Iio i).filter (fun k ↦ x k = x i)) ⊆
      (Finset.Iio j).filter (fun k ↦ x k = x i) := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simp [hij]
    · obtain ⟨hk, he⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr ((Finset.mem_Iio.mp hk).trans hij), he⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hi] at hc
  exact hc

lemma hasseDeriv_eval_eq_sum_fin {R : Type*} [CommRing R] (a : R) (k : ℕ)
    {n : ℕ} (P : R[X]) (hP : P.natDegree < n) :
    (hasseDeriv k P).eval a =
      ∑ j : Fin n, (j.val.choose k : R) * a ^ (j.val - k) * P.coeff j.val := by
  conv_lhs => rw [P.as_sum_range' n hP]
  rw [map_sum, eval_finsetSum, Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ (j.choose k : R) * a ^ (j - k) * P.coeff j)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [hasseDeriv_monomial, eval_monomial]
  ring

lemma confluentVandermonde_mul_coefficients {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (P : Fin n → R[X]) (hP : ∀ j, (P j).natDegree < n) :
    confluentVandermonde x * Matrix.of (fun i j : Fin n ↦ (P j).coeff i.val) =
      Matrix.of (fun i j ↦ (hasseDeriv (rootPrefixMultiplicity x i) (P j)).eval (x i)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [hasseDeriv_eval_eq_sum_fin _ _ _ (hP j)]
  rfl

lemma confluentVandermonde_newton_lowerTriangular {R : Type*} [CommRing R]
    {n : ℕ} (x : Fin n → R) :
    (Matrix.of (fun i j : Fin n ↦ (hasseDeriv (rootPrefixMultiplicity x i)
      (rootPrefixPolynomial x j)).eval (x i))).IsLowerTriangular := by
  intro i j hij
  exact hasseDeriv_prod_X_sub_C_eval_eq_zero_of_lt _ _ _
    (rootPrefixMultiplicity_lt_later_count x hij)

lemma confluentVandermonde_newton_diagonal {R : Type*} [CommRing R]
    {n : ℕ} (x : Fin n → R) (i : Fin n) :
    (hasseDeriv (rootPrefixMultiplicity x i) (rootPrefixPolynomial x i)).eval (x i) =
      ∏ j ∈ (Finset.Iio i).filter (fun j ↦ x j ≠ x i), (x i - x j) := by
  exact hasseDeriv_prod_X_sub_C_eval_multiplicity _ _ _

lemma det_confluentVandermonde {R : Type*} [CommRing R] [Nontrivial R]
    {n : ℕ} (x : Fin n → R) :
    (confluentVandermonde x).det =
      ∏ i : Fin n, ∏ j ∈ (Finset.Iio i).filter (fun j ↦ x j ≠ x i), (x i - x j) := by
  have hc : (Matrix.of (fun i j : Fin n ↦ (rootPrefixPolynomial x j).coeff i.val)).det = 1 :=
    Matrix.det_matrixOfPolynomials _ (rootPrefixPolynomial_natDegree x) (rootPrefixPolynomial_monic x)
  have he := congrArg Matrix.det (confluentVandermonde_mul_coefficients x
    (rootPrefixPolynomial x) (fun j ↦ (rootPrefixPolynomial_natDegree x j).trans_lt j.isLt))
  rw [Matrix.det_mul, hc, mul_one,
    Matrix.det_of_isLowerTriangular _ (confluentVandermonde_newton_lowerTriangular x)] at he
  rw [he]
  exact Finset.prod_congr rfl (fun i _ ↦ confluentVandermonde_newton_diagonal x i)

lemma det_confluentVandermonde_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (x : Fin n → R) : (confluentVandermonde x).det ≠ 0 := by
  rw [det_confluentVandermonde]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (Finset.mem_filter.mp hj).2.symm

end OdlyzkoPoonen
