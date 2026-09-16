import OdlyzkoPoonen.Analysis.PolynomialRootPowers
import OdlyzkoPoonen.Analysis.MahlerRootPowers
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Mahler products for repeated powered roots

The product of max(1, root norm) over a family of powered roots is an exact
power of the original polynomial's Mahler measure. Copy counts and exponents
are summed explicitly, so the estimate is independent of the node ordering.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

lemma prod_max_norm_root_powers {β : Type*} [Fintype β] (α : β → ℂ) (r : ℕ) :
    (∏ a, max 1 ‖α a ^ r‖) = (∏ a, max 1 ‖α a‖) ^ r := by
  simp only [max_one_norm_pow, Finset.prod_pow]

lemma prod_max_norm_eq_mahler_of_factorization {β : Type*} [Fintype β]
    (α : β → ℂ) {f : ℂ[X]} (hf : f = ∏ a, (X - C (α a))) :
    (∏ a, max 1 ‖α a‖) = f.mahlerMeasure := by
  rw [hf]
  simp only [Finset.prod_eq_multiset_prod]
  rw [prod_mahlerMeasure_eq_mahlerMeasure_prod]
  simp only [Multiset.map_map, Function.comp_def, mahlerMeasure_X_sub_C]

lemma prod_max_norm_repeated_root_powers {ι β : Type*} [Fintype ι] [Fintype β]
    (w r : ι → ℕ) (α : β → ℂ) {f : ℂ[X]}
    (hf : f = ∏ a, (X - C (α a))) {n : ℕ}
    (e : Fin n ≃ (Σ t, Fin (w t) × β)) :
    (∏ i, max 1 ‖α (e i).2.2 ^ r (e i).1‖) =
      f.mahlerMeasure ^ (∑ t, r t * w t) := by
  calc
    _ = ∏ j : (Σ t, Fin (w t) × β), max 1 ‖α j.2.2 ^ r j.1‖ :=
      e.prod_comp (fun j ↦ max 1 ‖α j.2.2 ^ r j.1‖)
    _ = ∏ t, (∏ a, max 1 ‖α a ^ r t‖) ^ w t := by
      simp only [Fintype.prod_sigma, Fintype.prod_prod_type, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    _ = ∏ t, f.mahlerMeasure ^ (r t * w t) := by
      simp only [prod_max_norm_root_powers, prod_max_norm_eq_mahler_of_factorization α hf,
        ← pow_mul]
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

lemma prod_max_norm_option_root_powers {ι β : Type*} [Fintype ι] [Fintype β]
    (k : ℕ) (p : ι → ℕ) (α : β → ℂ) {f : ℂ[X]}
    (hf : f = ∏ a, (X - C (α a))) {n : ℕ}
    (e : Fin n ≃ (Σ t : Option ι, Fin (t.elim k (fun _ ↦ 1)) × β)) :
    (∏ i, max 1 ‖α (e i).2.2 ^ (e i).1.elim 1 p‖) =
      f.mahlerMeasure ^ (k + ∑ i, p i) := by
  rw [prod_max_norm_repeated_root_powers (fun t : Option ι ↦ t.elim k (fun _ ↦ 1))
    (fun t ↦ t.elim 1 p) α hf e]
  simp [Fintype.sum_option]

end OdlyzkoPoonen
