import OdlyzkoPoonen.Polynomial.TaylorRootProducts
import OdlyzkoPoonen.Polynomial.IntegerResultantBounds

/-!
# Resultants as finite products of root differences

These identities let a determinant indexed by explicit root families be grouped
into integer cross-resultants and derivative resultants. Injectivity is needed
only for the within-family derivative formula.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma resultant_prod_X_sub_C {ι R : Type*} [Fintype ι] [CommRing R] [IsDomain R]
    (x : ι → R) (Q : R[X]) :
    resultant (∏ i, (X - C (x i))) Q = ∏ i, Q.eval (x i) := by
  rw [resultant_prod_left _ _ _ _ (by simp) le_rfl]
  simp only [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ le_rfl]

lemma norm_resultant_eq_root_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℂ) (y : κ → ℂ) {f g : ℂ[X]}
    (hf : f = ∏ i, (X - C (x i))) (hg : g = ∏ j, (X - C (y j))) :
    ‖resultant f g‖ = ∏ i, ∏ j, ‖x i - y j‖ := by
  rw [hf, resultant_prod_X_sub_C, hg, norm_prod]
  simp only [eval_prod, eval_sub, eval_X, eval_C, norm_prod]

lemma eval_derivative_prod_X_sub_C {ι R : Type*} [Fintype ι] [CommRing R]
    (x : ι → R) (hx : Function.Injective x) (i : ι) :
    (derivative (∏ j, (X - C (x j)))).eval (x i) =
      ∏ j, if x i = x j then (1 : R) else x i - x j := by
  have hc : (Finset.univ.filter (fun j ↦ x j = x i)).card = 1 := by
    have he : Finset.univ.filter (fun j ↦ x j = x i) = {i} := by
      ext j
      simp [hx.eq_iff]
    rw [he, Finset.card_singleton]
  have h := hasseDeriv_prod_X_sub_C_eval_multiplicity Finset.univ x (x i)
  rw [hc, hasseDeriv_one, Finset.prod_filter] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases he : x j = x i
  · rw [ite_eq_right (not_not_intro he), ite_eq_left he.symm]
  · rw [ite_eq_left he, ite_eq_right (Ne.symm he)]

lemma norm_resultant_derivative_eq_root_product {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hx : Function.Injective x) {f : ℂ[X]}
    (hf : f = ∏ i, (X - C (x i))) :
    ‖resultant f f.derivative‖ =
      ∏ i, ∏ j, if x i = x j then (1 : ℝ) else ‖x i - x j‖ := by
  rw [hf, resultant_prod_X_sub_C, norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [eval_derivative_prod_X_sub_C x hx, norm_prod]
  apply Finset.prod_congr rfl
  intro j hj
  split_ifs <;> simp

end OdlyzkoPoonen
