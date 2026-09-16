import OdlyzkoPoonen.Polynomial.RootBound

/-!
# Coefficient bounds from bounded roots

Multiplication by `X - z` increases a uniform coefficient bound by at most
`1 + ‖z‖`. Induction over the actual root multiset therefore bounds every
coefficient of a monic degree-`h` polynomial with roots of norm at most two by
`3^h`. Applying the strict root bound to a divisor gives the integer estimate
used to count possible small-degree factors.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma norm_coeff_mul_X_sub_C_le {p : ℂ[X]} {B : ℝ} (hB : 0 ≤ B)
    (hp : ∀ k, ‖p.coeff k‖ ≤ B) (z : ℂ) (k : ℕ) :
    ‖((X - C z) * p).coeff k‖ ≤ (1 + ‖z‖) * B := by
  rw [sub_mul, coeff_sub, coeff_C_mul]
  have hx : ‖(X * p).coeff k‖ ≤ B := by
    cases k with
    | zero => simpa only [coeff_X_mul_zero, norm_zero] using hB
    | succ k => simpa only [coeff_X_mul] using hp k
  calc
    _ ≤ ‖(X * p).coeff k‖ + ‖z * p.coeff k‖ := norm_sub_le _ _
    _ ≤ B + ‖z‖ * B := add_le_add hx (by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hp k) (norm_nonneg z))
    _ = _ := by ring

lemma norm_coeff_prod_X_sub_C_le (s : Multiset ℂ)
    (hs : ∀ z ∈ s, ‖z‖ ≤ 2) (k : ℕ) :
    ‖((s.map (fun z ↦ X - C z)).prod).coeff k‖ ≤ (3 : ℝ) ^ s.card := by
  revert hs k
  induction s using Multiset.induction_on with
  | empty =>
    intro _ k
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero, coeff_one]
    split_ifs <;> norm_num
  | @cons z s ih =>
    intro hs k
    have hz : ‖z‖ ≤ 2 := hs z (Multiset.mem_cons_self z s)
    have hrest : ∀ w ∈ s, ‖w‖ ≤ 2 :=
      fun w hw ↦ hs w (Multiset.mem_cons_of_mem hw)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc
      _ ≤ (1 + ‖z‖) * (3 : ℝ) ^ s.card :=
        norm_coeff_mul_X_sub_C_le (by positivity) (ih hrest) z k
      _ ≤ 3 * (3 : ℝ) ^ s.card :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := mul_comm _ _

lemma monic_coeff_norm_le_of_roots_le_two {p : ℂ[X]} (hp : p.Monic)
    (hr : ∀ z ∈ p.roots, ‖z‖ ≤ 2) (k : ℕ) :
    ‖p.coeff k‖ ≤ (3 : ℝ) ^ p.natDegree := by
  have he := (IsAlgClosed.splits p).eq_prod_roots_of_monic hp
  have h := norm_coeff_prod_X_sub_C_le p.roots hr k
  rw [← he, IsAlgClosed.card_roots_eq_natDegree] at h
  exact h

lemma HasBinaryEndpoints.monic_divisor_coeff_abs_le {n : ℕ} {p J : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hJ : J.Monic) (hdvd : J ∣ p) (k : ℕ) :
    |J.coeff k| ≤ (3 : ℤ) ^ J.natDegree := by
  have hm := hJ.map (Int.castRingHom ℂ)
  have hr : ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots, ‖z‖ ≤ 2 := by
    intro z hz
    have he : (J.map (Int.castRingHom ℂ)).eval z = 0 := (mem_roots hm.ne_zero).mp hz
    rw [eval_map] at he
    exact (hp.divisor_root_norm_lt_two hdvd he).le
  have h := monic_coeff_norm_le_of_roots_le_two hm hr k
  rw [coeff_map, hJ.natDegree_map] at h
  change ‖(J.coeff k : ℂ)‖ ≤ (3 : ℝ) ^ J.natDegree at h
  rw [Complex.norm_intCast] at h
  exact_mod_cast h

end OdlyzkoPoonen
