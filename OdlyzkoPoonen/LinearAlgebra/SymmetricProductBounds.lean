import Mathlib.Tactic

/-!
# Keeping one row and column in a positive symmetric product

When every factor is at least one, all factors outside a distinguished row and
column can be discarded in a lower bound. The remaining two equal products
supply the square used in the confluent determinant estimate.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma option_symmetric_prod_lower {ι : Type*} [Fintype ι]
    (A : Option ι → Option ι → ℝ) (hA : ∀ t u, 1 ≤ A t u)
    (hsym : ∀ t u, A t u = A u t) (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hc : ∀ i, c i ≤ A (some i) none) :
    (∏ i, c i) ^ 2 ≤ ∏ t, ∏ u, A t u := by
  classical
  let B : Option ι → Option ι → ℝ := fun t u ↦
    match t, u with
    | none, some i => c i
    | some i, none => c i
    | _, _ => 1
  have hB0 (t u : Option ι) : 0 ≤ B t u := by
    cases t <;> cases u <;> simp [B, hc0]
  have hBA (t u : Option ι) : B t u ≤ A t u := by
    cases t with
    | none =>
      cases u with
      | none => exact hA _ _
      | some i => simpa only [B, hsym none (some i)] using hc i
    | some i =>
      cases u with
      | none => exact hc i
      | some j => exact hA _ _
  have h : (∏ t, ∏ u, B t u) ≤ ∏ t, ∏ u, A t u := Finset.prod_le_prod₀ (fun t _ ↦ Finset.prod_nonneg (fun u _ ↦ hB0 t u))
    (fun t _ ↦ Finset.prod_le_prod₀ (fun u _ ↦ hB0 t u) (fun u _ ↦ hBA t u))
  have he : (∏ t, ∏ u, B t u) = (∏ i, c i) ^ 2 := by
    simp [Fintype.prod_option, B, pow_two]
  rwa [he] at h

end OdlyzkoPoonen
