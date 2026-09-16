import OdlyzkoPoonen.Polynomial.RootProductResultants

/-!
# Lower bounds for simple integer root families

All nonzero integer resultants have norm at least one. For a simple integer
root family this applies to its derivative resultant, including degree zero.
No discriminant lower bound from outside the library is needed.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma one_le_norm_derivative_resultant_of_integer_root_family
    {ι : Type*} [Fintype ι] (J : ℤ[X]) (x : ι → ℂ)
    (hx : Function.Injective x)
    (hJ : J.map (Int.castRingHom ℂ) = ∏ i, (X - C (x i))) :
    1 ≤ ‖resultant (J.map (Int.castRingHom ℂ))
      (J.map (Int.castRingHom ℂ)).derivative‖ := by
  have hpos : 0 < ‖resultant (J.map (Int.castRingHom ℂ))
      (J.map (Int.castRingHom ℂ)).derivative‖ := by
    rw [norm_resultant_derivative_eq_root_product x hx hJ]
    apply Finset.prod_pos
    intro i hi
    apply Finset.prod_pos
    intro j hj
    split_ifs with he
    · exact zero_lt_one
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr he)
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have he : resultant (J.map (Int.castRingHom ℂ))
      (J.map (Int.castRingHom ℂ)).derivative = ((resultant J J.derivative : ℤ) : ℂ) := by
    rw [derivative_map, resultant_map_injective _ hinj]
    rfl
  rw [he] at hpos ⊢
  have hz : resultant J J.derivative ≠ 0 := by
    intro hz
    simp only [hz, Int.cast_zero, norm_zero, lt_self_iff_false] at hpos
  simpa only [Nat.cast_one] using nat_le_norm_intCast_of_dvd (a := 1) (by simp) hz

lemma root_families_disjoint_of_isCoprime {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℂ) (y : κ → ℂ) {f g : ℂ[X]}
    (hf : f = ∏ i, (X - C (x i))) (hg : g = ∏ j, (X - C (y j)))
    (hc : IsCoprime f g) (i : ι) (j : κ) : x i ≠ y j := by
  intro he
  have hfz : f.eval (x i) = 0 := by
    rw [hf, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have hgz : g.eval (x i) = 0 := by
    rw [hg, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [he]
  have h := (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ f g).mp hc (x i)
  exact h.elim (fun h ↦ h hfz) (fun h ↦ h hgz)

end OdlyzkoPoonen
