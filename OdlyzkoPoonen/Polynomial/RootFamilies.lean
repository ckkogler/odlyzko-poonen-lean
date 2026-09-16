import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Enumerating a simple complex root multiset

A monic polynomial with no repeated roots admits an injective family indexed
by its natural degree. Both membership in the actual root multiset and the
factorization into linear factors are retained explicitly.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma exists_injective_complex_root_family {f : ℂ[X]} (hf : f.Monic)
    (hn : f.roots.Nodup) :
    ∃ x : Fin f.natDegree → ℂ, Function.Injective x ∧
      (∀ i, x i ∈ f.roots) ∧ f = ∏ i, (X - C (x i)) := by
  let S := f.roots.toFinset
  have hc : Fintype.card S = f.natDegree := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hn,
      ← (IsAlgClosed.splits f).natDegree_eq_card_roots]
  let e : Fin f.natDegree ≃ S := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨(fun i ↦ (e i : ℂ)), Subtype.val_injective.comp e.injective, ?_, ?_⟩
  · intro i
    exact Multiset.mem_toFinset.mp (e i).property
  · calc
      f = (f.roots.map (fun z ↦ X - C z)).prod :=
        (IsAlgClosed.splits f).eq_prod_roots_of_monic hf
      _ = ∏ z ∈ S, (X - C z) := by
        rw [Finset.prod_eq_multiset_prod]
        dsimp [S]
        rw [hn.dedup]
      _ = ∏ z : S, (X - C (z : ℂ)) := (Finset.prod_coe_sort _ _).symm
      _ = ∏ i : Fin f.natDegree, (X - C (e i : ℂ)) :=
        (e.prod_comp (fun z : S ↦ (X - C (z : ℂ)))).symm

end OdlyzkoPoonen
