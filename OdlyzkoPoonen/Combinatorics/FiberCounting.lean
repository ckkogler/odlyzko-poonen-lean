import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace OdlyzkoPoonen

/-- A finite map with fibers of size at most two has image size at least half
the size of its domain. -/
lemma card_le_twice_image_of_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β)
    (h : ∀ y ∈ s.image f, (s.filter (fun x ↦ f x = y)).card ≤ 2) :
    s.card ≤ 2 * (s.image f).card := by
  calc
    s.card = ∑ y ∈ s.image f, (s.filter (fun x ↦ f x = y)).card :=
      Finset.card_eq_sum_card_image f s
    _ ≤ ∑ _y ∈ s.image f, 2 := Finset.sum_le_sum h
    _ = 2 * (s.image f).card := by simp [Nat.mul_comm]

/-- If a finite map is invariant under a self-map, the number of image values
is at most half the domain size plus half the number of fixed points.
The map need not be injective, and a fiber may contain several orbits. -/
lemma twice_image_card_le_card_add_fixed {α β : Type*}
    [DecidableEq α] [DecidableEq β] (s : Finset α) (f : α → β) (r : α → α)
    (hr : ∀ x ∈ s, r x ∈ s) (hf : ∀ x ∈ s, f (r x) = f x) :
    2 * (s.image f).card ≤ s.card + (s.filter (fun x ↦ r x = x)).card := by
  classical
  have hfiber (y : β) (hy : y ∈ s.image f) :
      2 ≤ (s.filter (fun x ↦ f x = y)).card +
        ((s.filter (fun x ↦ r x = x)).filter (fun x ↦ f x = y)).card := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hxF : x ∈ s.filter (fun z ↦ f z = f x) := by simp [hx]
    have hrF : r x ∈ s.filter (fun z ↦ f z = f x) := by simp [hr x hx, hf x hx]
    by_cases he : r x = x
    · have hpos := Finset.card_pos.mpr ⟨x, hxF⟩
      have hfix : 0 < ((s.filter (fun z ↦ r z = z)).filter
          (fun z ↦ f z = f x)).card :=
        Finset.card_pos.mpr ⟨x, by simp [hx, he]⟩
      omega
    · have hsub : ({x, r x} : Finset α) ⊆ s.filter (fun z ↦ f z = f x) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hxF
        · exact hrF
      have htwo : 2 ≤ (s.filter (fun z ↦ f z = f x)).card := by
        simpa [Ne.symm he] using Finset.card_le_card hsub
      omega
  have hsum := Finset.sum_le_sum hfiber
  have hfixed : ∑ y ∈ s.image f,
      ((s.filter (fun x ↦ r x = x)).filter (fun x ↦ f x = y)).card =
        (s.filter (fun x ↦ r x = x)).card := by
    symm
    apply Finset.card_eq_sum_card_fiberwise
    intro x hx
    exact Finset.mem_image_of_mem f (Finset.mem_filter.mp hx).1
  rw [Finset.sum_add_distrib, ← Finset.card_eq_sum_card_image, hfixed] at hsum
  simpa [Nat.mul_comm] using hsum

end OdlyzkoPoonen
