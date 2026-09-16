import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# An elementary determinant bound from row bounds

The Leibniz formula and the triangle inequality give `n!` times the product
of row bounds. This coarse estimate suffices for the logarithmic-cubic Mahler
argument and avoids needing a sharp Hadamard inequality.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma norm_det_le_factorial_mul_prod {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℝ) (hA : ∀ i j, ‖A i j‖ ≤ b i) :
    ‖A.det‖ ≤ (n.factorial : ℝ) * ∏ i, b i := by
  classical
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ i, b i := by
      apply Finset.sum_le_sum
      intro σ hσ
      have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
      rw [norm_mul, hs, one_mul, norm_prod]
      calc
        _ ≤ ∏ i, b (σ i) := Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) (fun i _ ↦ hA _ _)
        _ = _ := Equiv.prod_comp σ b
    _ = _ := by simp [Fintype.card_perm]

end OdlyzkoPoonen
