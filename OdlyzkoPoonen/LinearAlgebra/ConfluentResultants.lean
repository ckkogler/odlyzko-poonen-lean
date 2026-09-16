import OdlyzkoPoonen.LinearAlgebra.ConfluentVandermondeProducts
import OdlyzkoPoonen.LinearAlgebra.RepeatedProducts
import OdlyzkoPoonen.Polynomial.RootProductResultants

/-!
# Grouping a confluent determinant into resultants

Each group is a simple root family of a polynomial. Distinct groups have no
common root, and every root in group `t` is repeated `w t` times. The squared
norm of the confluent determinant is the product of derivative resultants on
the diagonal and cross-resultants off the diagonal, with multiplicities
`w t * w u`. The node ordering may be any enumeration of this finite family.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma norm_det_confluent_eq_resultant_product {ι : Type*} [Fintype ι]
    {β : ι → Type*} [∀ t, Fintype (β t)] (w : ι → ℕ)
    (x : ∀ t, β t → ℂ) (f : ι → ℂ[X])
    (hf : ∀ t, f t = ∏ a, (X - C (x t a)))
    (hx : ∀ t, Function.Injective (x t))
    (hdisj : ∀ t u, t ≠ u → ∀ a b, x t a ≠ x u b)
    {n : ℕ} (e : Fin n ≃ (Σ t, Fin (w t) × β t)) :
    ‖(confluentVandermonde (fun i ↦ x (e i).1 (e i).2.2)).det‖ ^ 2 =
      ∏ t, ∏ u, (if t = u then ‖resultant (f t) (f t).derivative‖
        else ‖resultant (f t) (f u)‖) ^ (w t * w u) := by
  have he := norm_det_confluentVandermonde_sq_equiv e (fun i ↦ x i.1 i.2.2)
  simp only [Function.comp_def] at he
  rw [he, prod_repeated_pairs w (fun t a u b ↦
      if x t a = x u b then (1 : ℝ) else ‖x t a - x u b‖)]
  apply Finset.prod_congr rfl
  intro t ht
  apply Finset.prod_congr rfl
  intro u hu
  congr 1
  by_cases htu : t = u
  · subst u
    rw [ite_eq_left rfl, norm_resultant_derivative_eq_root_product _ (hx t) (hf t)]
  · rw [ite_eq_right htu, norm_resultant_eq_root_product _ _ (hf t) (hf u)]
    apply Finset.prod_congr rfl
    intro a ha
    apply Finset.prod_congr rfl
    intro b hb
    exact ite_eq_right (hdisj t u htu a b)

end OdlyzkoPoonen
