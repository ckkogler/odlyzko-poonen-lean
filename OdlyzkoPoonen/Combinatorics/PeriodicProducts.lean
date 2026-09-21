import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Grouping finite products of a periodic sequence

Complete periods contribute fixed powers; a final incomplete period remains
independent of the number of complete blocks. Cyclic shifts preserve the
one-period product without requiring any factor to be nonzero.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma periodic_nat_add_mul {α : Type*} {v : ℕ → α} {q : ℕ}
    (hv : ∀ j, v (j + q) = v j) (j k : ℕ) : v (j + q * k) = v j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, hv, ih]

theorem periodic_prod_blocks {M : Type*} [CommMonoid M] (g : ℕ → M) (q : ℕ)
    (hg : ∀ j, g (j + q) = g j) (k r : ℕ) :
    (∏ j ∈ Finset.range (q * k + r), g j) =
      (∏ j ∈ Finset.range q, g j) ^ k * ∏ j ∈ Finset.range r, g j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show q * (k + 1) + r = q + (q * k + r) by ring, Finset.prod_range_add]
    have he : (∏ j ∈ Finset.range (q * k + r), g (q + j)) =
        ∏ j ∈ Finset.range (q * k + r), g j := by
      apply Finset.prod_congr rfl
      intro j _
      simpa only [Nat.add_comm] using hg j
    rw [he, ih, pow_succ]
    ac_rfl

lemma periodic_prod_shift {M : Type*} [CommMonoid M] (g : ℕ → M) {q : ℕ}
    (hq : 0 < q) (hg : g q = g 0) :
    (∏ j ∈ Finset.range q, g (j + 1)) = ∏ j ∈ Finset.range q, g j := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  rw [Finset.prod_range_succ, Finset.prod_range_succ' g]
  rw [hg]

theorem periodic_prod_blocks_shift {M : Type*} [CommMonoid M] (g : ℕ → M)
    {q : ℕ} (hq : 0 < q) (hg : ∀ j, g (j + q) = g j) (k r : ℕ) :
    (∏ j ∈ Finset.range (q * k + r), g (j + 1)) =
      (∏ j ∈ Finset.range q, g j) ^ k * ∏ j ∈ Finset.range r, g (j + 1) := by
  rw [periodic_prod_blocks (fun j ↦ g (j + 1)) q
    (fun j ↦ by simpa only [Nat.add_right_comm] using hg (j + 1)) k r,
    periodic_prod_shift g hq (by simpa using hg 0)]

end OdlyzkoPoonen
