import OdlyzkoPoonen.LinearAlgebra.ConfluentVandermonde
import OdlyzkoPoonen.LinearAlgebra.SymmetricProducts
import Mathlib.Analysis.Complex.Basic

/-!
# The squared confluent determinant as a symmetric root product

Unequal pairs contribute their distance and equal pairs contribute one. The
full pair product is independent of the order of the nodes, and retains all
multiplicities of distinct roots.
-/

noncomputable section
namespace OdlyzkoPoonen
open scoped BigOperators Classical

lemma norm_det_confluentVandermonde_sq {n : ℕ} (x : Fin n → ℂ) :
    ‖(confluentVandermonde x).det‖ ^ 2 =
      ∏ i, ∏ j, if x i = x j then (1 : ℝ) else ‖x i - x j‖ := by
  rw [prod_symmetric_eq_lower_sq _
    (fun i j ↦ by
      by_cases h : x i = x j
      · rw [ite_eq_left h, ite_eq_left h.symm]
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h), norm_sub_rev])
    (fun i ↦ by simp), det_confluentVandermonde, norm_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [norm_prod, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases h : x j = x i
  · rw [ite_eq_right (not_not_intro h), ite_eq_left h.symm]
  · rw [ite_eq_left h, ite_eq_right (Ne.symm h)]

lemma norm_det_confluentVandermonde_sq_equiv {ι : Type*} [Fintype ι]
    {n : ℕ} (e : Fin n ≃ ι) (x : ι → ℂ) :
    ‖(confluentVandermonde (x ∘ e)).det‖ ^ 2 =
      ∏ i, ∏ j, if x i = x j then (1 : ℝ) else ‖x i - x j‖ := by
  rw [norm_det_confluentVandermonde_sq]
  simp only [Function.comp_apply]
  calc
    _ = ∏ i : Fin n, ∏ j : ι,
        if x (e i) = x j then (1 : ℝ) else ‖x (e i) - x j‖ := by
      apply Finset.prod_congr rfl
      intro i hi
      exact e.prod_comp (fun j : ι ↦ if x (e i) = x j then (1 : ℝ) else ‖x (e i) - x j‖)
    _ = _ := e.prod_comp (fun i : ι ↦ ∏ j, if x i = x j then (1 : ℝ) else ‖x i - x j‖)

end OdlyzkoPoonen
