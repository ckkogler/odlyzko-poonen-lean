import OdlyzkoPoonen.Combinatorics.DifferenceMultisetCount
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Difference multisets with a free upper endpoint

Subsets of `{0, ..., n}` containing zero decompose by their largest element.
The largest signed difference recovers that element, so the corresponding
families of difference multisets are disjoint.
-/

namespace OdlyzkoPoonen
open scoped BigOperators Classical

/-- Subsets containing zero, with no condition at the upper endpoint. -/
def anchoredSetFamily (n : ℕ) : Finset (Finset ℕ) :=
  ((Finset.range (n + 1)).powerset).filter (fun A ↦ 0 ∈ A)

lemma mem_anchoredSetFamily_iff {n : ℕ} {A : Finset ℕ} :
    A ∈ anchoredSetFamily n ↔ (∀ a ∈ A, a ≤ n) ∧ 0 ∈ A := by
  simp only [anchoredSetFamily, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_iff, Finset.mem_range, Nat.lt_succ_iff]

/-- Distinct signed difference multisets of subsets containing zero. -/
noncomputable def anchoredDifferenceMultisetFamily (n : ℕ) : Finset (Multiset ℤ) :=
  (anchoredSetFamily n).image differenceMultiset

lemma differenceMultiset_mem_iff {A : Finset ℕ} {z : ℤ} :
    z ∈ differenceMultiset A ↔ ∃ a ∈ A, ∃ b ∈ A, (a : ℤ) - (b : ℤ) = z := by
  simp only [differenceMultiset, Multiset.mem_map, Finset.mem_val,
    Prod.exists]
  aesop

lemma endpoint_mem_differenceMultiset {n : ℕ} {A : Finset ℕ}
    (hA : A ∈ binarySetFamily n) : (n : ℤ) ∈ differenceMultiset A := by
  obtain ⟨_, hzero, htop⟩ := mem_binarySetFamily_iff.mp hA
  exact differenceMultiset_mem_iff.mpr ⟨n, htop, 0, hzero, by simp⟩

lemma differenceMultiset_mem_le {n : ℕ} {A : Finset ℕ}
    (hA : A ∈ binarySetFamily n) {z : ℤ} (hz : z ∈ differenceMultiset A) :
    z ≤ (n : ℤ) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := differenceMultiset_mem_iff.mp hz
  have := (mem_binarySetFamily_iff.mp hA).1 a ha
  omega

lemma differenceMultisetFamily_disjoint {n m : ℕ} (hnm : n ≠ m) :
    Disjoint (differenceMultisetFamily n) (differenceMultisetFamily m) := by
  apply Finset.disjoint_left.mpr
  intro D hDn hDm
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hDn
  obtain ⟨B, hB, hBA⟩ := Finset.mem_image.mp hDm
  have hn : (n : ℤ) ≤ m := differenceMultiset_mem_le hB
    (hBA.symm ▸ endpoint_mem_differenceMultiset hA)
  have hm : (m : ℤ) ≤ n := differenceMultiset_mem_le hA
    (hBA ▸ endpoint_mem_differenceMultiset hB)
  exact hnm (by omega)

theorem anchoredDifferenceMultisetFamily_eq_biUnion (n : ℕ) :
    anchoredDifferenceMultisetFamily n =
      (Finset.range (n + 1)).biUnion differenceMultisetFamily := by
  ext D
  constructor
  · intro hD
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨hbound, hzero⟩ := mem_anchoredSetFamily_iff.mp hA
    have hmax : A.sup id ∈ A := by
      simpa using Finset.sup_mem_of_nonempty (f := id) (show A.Nonempty from ⟨0, hzero⟩)
    have hsup : A.sup id ≤ n := Finset.sup_le hbound
    apply Finset.mem_biUnion.mpr
    refine ⟨A.sup id, Finset.mem_range.mpr (Nat.lt_succ_of_le hsup), ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨A, mem_binarySetFamily_iff.mpr
      ⟨fun a ha ↦ Finset.le_sup (f := id) ha, hzero, hmax⟩, rfl⟩
  · intro hD
    obtain ⟨d, hd, hDd⟩ := Finset.mem_biUnion.mp hD
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hDd
    apply Finset.mem_image.mpr
    obtain ⟨hbound, hzero, _⟩ := mem_binarySetFamily_iff.mp hA
    refine ⟨A, mem_anchoredSetFamily_iff.mpr ⟨?_, hzero⟩, rfl⟩
    intro a ha
    have := hbound a ha
    have := Finset.mem_range.mp hd
    omega

theorem card_anchoredDifferenceMultisetFamily (n : ℕ) :
    (anchoredDifferenceMultisetFamily n).card =
      ∑ d ∈ Finset.range (n + 1), (differenceMultisetFamily d).card := by
  rw [anchoredDifferenceMultisetFamily_eq_biUnion]
  apply Finset.card_biUnion
  intro i hi j hj hij
  exact differenceMultisetFamily_disjoint hij

lemma binarySetFamily_zero : binarySetFamily 0 = {{0}} := by
  ext A
  rw [mem_binarySetFamily_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨h, hzero, _⟩
    apply Finset.ext
    intro a
    simp only [Finset.mem_singleton]
    constructor
    · intro ha
      exact Nat.eq_zero_of_le_zero (h a ha)
    · rintro rfl
      exact hzero
  · rintro rfl
    simp

lemma card_differenceMultisetFamily_zero : (differenceMultisetFamily 0).card = 1 := by
  simp [differenceMultisetFamily, binarySetFamily_zero]

theorem card_anchoredDifferenceMultisetFamily_succ_sum (n : ℕ) :
    (anchoredDifferenceMultisetFamily n).card =
      1 + ∑ d ∈ Finset.range n, (differenceMultisetFamily (d + 1)).card := by
  rw [card_anchoredDifferenceMultisetFamily, Finset.sum_range_succ',
    card_differenceMultisetFamily_zero, add_comm]

end OdlyzkoPoonen
