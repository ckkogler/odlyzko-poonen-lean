import OdlyzkoPoonen.Probability.UniformAverage

/-!
# Bounds for finite uniform averages

A constant has the same average on every nonempty finite type. In particular,
an upper bound independent of a fiber coordinate survives averaging over it.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (t : ℝ) :
    uniformAverage (fun _ : α ↦ t) = t := by
  unfold uniformAverage
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ t (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

lemma uniformAverage_le {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℝ} {t : ℝ} (h : ∀ a, f a ≤ t) : uniformAverage f ≤ t := by
  calc
    _ ≤ uniformAverage (fun _ : α ↦ t) := uniformAverage_mono h
    _ = t := uniformAverage_const t

end OdlyzkoPoonen
