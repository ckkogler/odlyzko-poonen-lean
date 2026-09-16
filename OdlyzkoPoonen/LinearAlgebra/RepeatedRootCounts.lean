import OdlyzkoPoonen.LinearAlgebra.ConfluentVandermonde
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Counting repeated root families

A family injective in the group/root pair has exactly `w t` occurrences of
root `(t,a)` when group `t` is copied `w t` times. This bounds each row's
previous-occurrence order and its sum without dependence on the enumeration.
-/

noncomputable section
namespace OdlyzkoPoonen
open scoped BigOperators Classical

lemma card_repeated_family {ι β : Type*} [Fintype ι] [Fintype β] (w : ι → ℕ) :
    Fintype.card (Σ t, Fin (w t) × β) = Fintype.card β * ∑ t, w t := by
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  rw [← Finset.sum_mul, Nat.mul_comm]

lemma repeated_root_fiber_count {ι β R : Type*} [Fintype ι] [Fintype β]
    (w : ι → ℕ) (x : ι → β → R)
    (hx : Function.Injective (fun z : ι × β ↦ x z.1 z.2)) (t : ι) (a : β) :
    (Finset.univ.filter (fun j : (Σ t, Fin (w t) × β) ↦ x j.1 j.2.2 = x t a)).card = w t := by
  have hxy (u : ι) (b : β) : x u b = x t a ↔ u = t ∧ b = a := by
    constructor
    · intro he
      exact Prod.mk.inj (hx he)
    · rintro ⟨rfl, rfl⟩
      rfl
  have he := Finset.sum_boole (R := ℕ)
    (fun j : (Σ t, Fin (w t) × β) ↦ x j.1 j.2.2 = x t a) Finset.univ
  simp only [Nat.cast_id] at he
  rw [← he]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, hxy]
  rw [Finset.sum_eq_single t]
  · simp
  · intro u hu hut
    simp [hut]
  · simp

lemma rootPrefixMultiplicity_repeated_le {ι β R : Type*} [Fintype ι] [Fintype β]
    (w : ι → ℕ) (x : ι → β → R)
    (hx : Function.Injective (fun z : ι × β ↦ x z.1 z.2))
    {n : ℕ} (e : Fin n ≃ (Σ t, Fin (w t) × β)) (i : Fin n) :
    rootPrefixMultiplicity (fun j ↦ x (e j).1 (e j).2.2) i ≤ w (e i).1 := by
  have he := e.sum_comp (fun j : (Σ t, Fin (w t) × β) ↦
    if x j.1 j.2.2 = x (e i).1 (e i).2.2 then (1 : ℕ) else 0)
  simp only [Finset.sum_boole, Nat.cast_id] at he
  rw [repeated_root_fiber_count w x hx] at he
  calc
    _ ≤ (Finset.univ.filter (fun j ↦ x (e j).1 (e j).2.2 = x (e i).1 (e i).2.2)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
    _ = _ := he

lemma sum_rootPrefixMultiplicity_repeated_le {ι β R : Type*} [Fintype ι] [Fintype β]
    (w : ι → ℕ) (x : ι → β → R)
    (hx : Function.Injective (fun z : ι × β ↦ x z.1 z.2))
    {n : ℕ} (e : Fin n ≃ (Σ t, Fin (w t) × β)) :
    (∑ i, rootPrefixMultiplicity (fun j ↦ x (e j).1 (e j).2.2) i) ≤
      Fintype.card β * ∑ t, w t ^ 2 := by
  calc
    _ ≤ ∑ i : Fin n, w (e i).1 :=
      Finset.sum_le_sum (fun i _ ↦ rootPrefixMultiplicity_repeated_le w x hx e i)
    _ = ∑ j : (Σ t, Fin (w t) × β), w j.1 := e.sum_comp (fun j ↦ w j.1)
    _ = _ := by
      simp only [Fintype.sum_sigma, Finset.sum_const,
        Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring

lemma card_repeated_option_family {ι β : Type*} [Fintype ι] [Fintype β] (k : ℕ) :
    Fintype.card (Σ t : Option ι, Fin (t.elim k (fun _ ↦ 1)) × β) =
      Fintype.card β * (k + Fintype.card ι) := by
  rw [card_repeated_family]
  simp [Fintype.sum_option]

end OdlyzkoPoonen
