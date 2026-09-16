import Mathlib.Tactic
import Mathlib.Data.Fin.Rev

/-!
# The degree-split geometric sum

The floor exponents are bounded below by `floor((n-1)/4)` and each occurs at
most twice. Reversing the split index gives a pointwise bound by a geometric
sequence with each term repeated twice. The resulting total is at most eight
times the initial power. All bounds include empty ranges.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

lemma sum_range_floor_half_even (s : ℕ) (q : ℝ) :
    (∑ i ∈ Finset.range (2 * s), q ^ (i / 2)) = 2 * ∑ i ∈ Finset.range s, q ^ i := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show 2 * (s + 1) = (2 * s + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih,
      show (2 * s + 1) / 2 = s by omega, show (2 * s) / 2 = s by omega,
      Finset.sum_range_succ]
    ring

lemma sum_three_quarters_range (s : ℕ) :
    (∑ i ∈ Finset.range s, (3 / 4 : ℝ) ^ i) = 4 * (1 - (3 / 4 : ℝ) ^ s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

lemma sum_floor_half_three_quarters_le_eight (s : ℕ) :
    (∑ i : Fin s, (3 / 4 : ℝ) ^ (i.val / 2)) ≤ 8 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (3 / 4 : ℝ) ^ (i / 2)) s]
  calc
    _ ≤ ∑ i ∈ Finset.range (2 * s), (3 / 4 : ℝ) ^ (i / 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun _ _ _ ↦ by positivity)
    _ = 2 * ∑ i ∈ Finset.range s, (3 / 4 : ℝ) ^ i := sum_range_floor_half_even s _
    _ ≤ 8 := by
      rw [sum_three_quarters_range]
      have h : 0 ≤ (3 / 4 : ℝ) ^ s := by positivity
      linarith

lemma companion_split_exponent_lower {n : ℕ} (i : Fin (n / 2)) :
    (n - 1) / 4 ≤ (n - (i.val + 1) - 1) / 2 := by
  have := i.isLt
  omega

lemma companion_split_exponent_reversed {n : ℕ} (i : Fin (n / 2)) :
    (n - 1) / 4 + i.val / 2 ≤ (n - (i.rev.val + 1) - 1) / 2 := by
  rw [Fin.val_rev]
  have := i.isLt
  omega

lemma companion_split_exponent_fiber_card_le_two (n k : ℕ) :
    (Finset.univ.filter (fun i : Fin (n / 2) ↦ (n - (i.val + 1) - 1) / 2 = k)).card ≤ 2 := by
  classical
  let f : Fin (n / 2) → ℕ := fun i ↦ n - (i.val + 1) - 1
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    dsimp [f] at h
    omega
  have hsub : (Finset.univ.filter (fun i : Fin (n / 2) ↦ f i / 2 = k)).image f ⊆
      {2 * k, 2 * k + 1} := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' := (Finset.mem_filter.mp hi).2
    have heq : f i = 2 * k ∨ f i = 2 * k + 1 := by omega
    simpa only [Finset.mem_insert, Finset.mem_singleton] using heq
  calc
    _ = ((Finset.univ.filter (fun i : Fin (n / 2) ↦ f i / 2 = k)).image f).card :=
      (Finset.card_image_of_injective _ hf).symm
    _ ≤ ({2 * k, 2 * k + 1} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 2 := by simp

lemma companion_split_sum_le_eight (n : ℕ) :
    (∑ i : Fin (n / 2), (3 / 4 : ℝ) ^ ((n - (i.val + 1) - 1) / 2)) ≤
      8 * (3 / 4 : ℝ) ^ ((n - 1) / 4) := by
  have hrev := Equiv.sum_comp (@Fin.revPerm (n / 2))
    (fun i : Fin (n / 2) ↦ (3 / 4 : ℝ) ^ ((n - (i.val + 1) - 1) / 2))
  rw [← hrev]
  calc
    _ ≤ ∑ i : Fin (n / 2), (3 / 4 : ℝ) ^ ((n - 1) / 4 + i.val / 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (companion_split_exponent_reversed i)
    _ = (3 / 4 : ℝ) ^ ((n - 1) / 4) * ∑ i : Fin (n / 2), (3 / 4 : ℝ) ^ (i.val / 2) := by
      simp only [pow_add, Finset.mul_sum]
    _ ≤ (3 / 4 : ℝ) ^ ((n - 1) / 4) * 8 :=
      mul_le_mul_of_nonneg_left (sum_floor_half_three_quarters_le_eight _) (by positivity)
    _ = _ := mul_comm _ _

end OdlyzkoPoonen
