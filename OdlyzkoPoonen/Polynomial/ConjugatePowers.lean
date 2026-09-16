import OdlyzkoPoonen.Polynomial.GaloisRoots
import Mathlib.Algebra.Group.Action.End

/-!
# Distinct powers of non-torsion conjugate roots

An automorphism permutes the finite root set. Iterating a power relation until
one root returns to itself forces equality of the exponents, unless a positive
power of the root is one. Only finiteness of the root set is used: the whole
normal extension need not be finite.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma pow_injective_of_no_positive_power_eq_one {K : Type*} [Field K] {a : K}
    (ha : a ≠ 0) (hno : ∀ k : ℕ, 0 < k → a ^ k ≠ 1) :
    Function.Injective (fun k : ℕ ↦ a ^ k) := by
  intro m n he
  change a ^ m = a ^ n at he
  wlog hmn : m ≤ n generalizing m n
  · exact (this he.symm (le_of_not_ge hmn)).symm
  by_contra hne
  have hlt : m < n := lt_of_le_of_ne hmn hne
  have hpow : a ^ m * a ^ (n - m) = a ^ m * 1 := by
    rw [← pow_add, Nat.add_sub_of_le hmn, ← he, mul_one]
  exact hno (n - m) (Nat.sub_pos_of_lt hlt) (mul_left_cancel₀ (pow_ne_zero _ ha) hpow)

lemma algEquiv_iterated_power_relation {F K : Type*} [Field F] [Field K]
    [Algebra F K] (σ : K ≃ₐ[F] K) {a : K} {r s : ℕ}
    (h : (σ a) ^ s = a ^ r) (m : ℕ) :
    ((σ ^ m) a) ^ (s ^ m) = a ^ (r ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      _ = (σ (((σ ^ m) a) ^ (s ^ m))) ^ s := by
        rw [pow_succ' σ, AlgEquiv.mul_apply, pow_succ s, pow_mul, map_pow]
      _ = (σ (a ^ (r ^ m))) ^ s := by rw [ih]
      _ = ((σ a) ^ s) ^ (r ^ m) := by rw [map_pow, pow_right_comm]
      _ = a ^ (r ^ (m + 1)) := by rw [h, ← pow_mul, pow_succ']

lemma exists_positive_algEquiv_power_fix_root {F K : Type*} [Field F] [Field K]
    [Algebra F K] {P : F[X]} (σ : K ≃ₐ[F] K) {a : K} (ha : a ∈ P.rootSet K) :
    ∃ m : ℕ, 0 < m ∧ (σ ^ m) a = a := by
  classical
  let ρ : (K ≃ₐ[F] K) →* Equiv.Perm (P.rootSet K) :=
    MulAction.toPermHom _ _
  refine ⟨orderOf (ρ σ), orderOf_pos _, ?_⟩
  have h : ρ (σ ^ orderOf (ρ σ)) = 1 := by rw [map_pow, pow_orderOf_eq_one]
  have hx := congrArg (fun τ : Equiv.Perm (P.rootSet K) ↦ (τ ⟨a, ha⟩).val) h
  exact hx

lemma eq_exponents_of_periodic_algEquiv_power_relation {F K : Type*} [Field F]
    [Field K] [Algebra F K] (σ : K ≃ₐ[F] K) {a : K} (ha : a ≠ 0)
    (hno : ∀ k : ℕ, 0 < k → a ^ k ≠ 1) {r s m : ℕ} (hm : 0 < m)
    (hperiod : (σ ^ m) a = a) (h : (σ a) ^ s = a ^ r) : r = s := by
  have he := algEquiv_iterated_power_relation σ h m
  rw [hperiod] at he
  have hnat := pow_injective_of_no_positive_power_eq_one ha hno he
  exact (Nat.pow_left_injective hm.ne' hnat).symm

lemma eq_exponents_of_conjugate_root_powers {F K : Type*} [Field F] [Field K]
    [Algebra F K] [Normal F K] {P : F[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) (hconst : P.coeff 0 ≠ 0) {a b : K}
    (ha : a ∈ P.rootSet K) (hb : b ∈ P.rootSet K)
    (hno : ∀ k : ℕ, 0 < k → a ^ k ≠ 1) {r s : ℕ} (he : a ^ r = b ^ s) : r = s := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_map_root hmonic hirr ha hb
  obtain ⟨m, hm, hperiod⟩ := exists_positive_algEquiv_power_fix_root σ ha
  exact eq_exponents_of_periodic_algEquiv_power_relation σ
    (root_ne_zero_of_constant_ne_zero hconst ha) hno hm hperiod (by rw [hσ]; exact he.symm)

end OdlyzkoPoonen
