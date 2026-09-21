import OdlyzkoPoonen.Polynomial.RemainderCoordinates
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic

/-!
# Explicit remainder tables for small cyclotomic divisors

Each finite table is verified by a polynomial divisibility witness and the
strict degree bound for the unique monic remainder.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

lemma power_modByMonic_eq_of_certificate {f r : ℤ[X]} (hf : f.Monic) (j : ℕ)
    (hr : r.degree < f.degree) (hd : f ∣ X ^ j - r) : (X : ℤ[X]) ^ j %ₘ f = r :=
  (modByMonic_eq_of_dvd_sub hf hd).trans ((modByMonic_eq_self_iff hf).mpr hr)

lemma cyclotomic_three_power_remainders (j : Fin 3) :
    (X : ℤ[X]) ^ j.val %ₘ cyclotomic 3 ℤ = ![1, X, -X - 1] j := by
  apply power_modByMonic_eq_of_certificate (cyclotomic.monic 3 ℤ)
  · have hd : (cyclotomic 3 ℤ).degree = 2 := by
      rw [degree_eq_natDegree (cyclotomic_ne_zero 3 ℤ), natDegree_cyclotomic]
      norm_num [show Nat.totient 3 = 2 by decide]
    rw [hd]
    fin_cases j <;> norm_num
    compute_degree!
  · rw [cyclotomic_three]
    fin_cases j
    · norm_num
    · norm_num
    · refine ⟨1, ?_⟩
      norm_num
      ring

lemma cyclotomic_four_int : cyclotomic 4 ℤ = (X : ℤ[X]) ^ 2 + 1 := by
  simpa [Finset.sum_range_succ, add_comm] using
    (cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (p := 2) (n := 1) Nat.prime_two)

lemma cyclotomic_four_power_remainders (j : Fin 4) :
    (X : ℤ[X]) ^ j.val %ₘ (cyclotomic 4 ℤ) =
      ![1, X, -1, -X] j := by
  apply power_modByMonic_eq_of_certificate
    ((cyclotomic.monic 4 ℤ))
  · have hd : (cyclotomic 4 ℤ).degree = 2 := by
      rw [cyclotomic_four_int]
      compute_degree!
    rw [hd]
    fin_cases j <;> norm_num <;> compute_degree!
  · refine ⟨![0, 0, 1, X] j, ?_⟩
    rw [cyclotomic_four_int]
    fin_cases j <;> norm_num
    ring

lemma cyclotomic_six_power_remainders (j : Fin 6) :
    (X : ℤ[X]) ^ j.val %ₘ (cyclotomic 6 ℤ) =
      ![1, X, X - 1, -1, -X, 1 - X] j := by
  apply power_modByMonic_eq_of_certificate
    ((cyclotomic.monic 6 ℤ))
  · have hd : (cyclotomic 6 ℤ).degree = 2 := by
      rw [cyclotomic_six]
      compute_degree!
    rw [hd]
    fin_cases j <;> norm_num <;> compute_degree!
  · refine ⟨![0, 0, 1, X + 1, X ^ 2 + X, X ^ 3 + X ^ 2 - 1] j, ?_⟩
    rw [cyclotomic_six]
    fin_cases j <;> norm_num <;> ring

lemma cyclotomic_two_three_power_remainders (j : Fin 6) :
    (X : ℤ[X]) ^ j.val %ₘ (cyclotomic 2 ℤ * cyclotomic 3 ℤ) =
      ![1, X, X ^ 2, -2 * X ^ 2 - 2 * X - 1, 2 * X ^ 2 + 3 * X + 2, -X ^ 2 - 2 * X - 2] j := by
  apply power_modByMonic_eq_of_certificate
    ((cyclotomic.monic 2 ℤ).mul (cyclotomic.monic 3 ℤ))
  · have hd : (cyclotomic 2 ℤ * cyclotomic 3 ℤ).degree = 3 := by
      rw [cyclotomic_two, cyclotomic_three]
      compute_degree!
    rw [hd]
    fin_cases j <;> norm_num <;> compute_degree!
  · refine ⟨![0, 0, 0, 1, X - 2, X ^ 2 - 2 * X + 2] j, ?_⟩
    rw [cyclotomic_two, cyclotomic_three]
    fin_cases j <;> norm_num <;> ring

lemma cyclotomic_two_four_power_remainders (j : Fin 4) :
    (X : ℤ[X]) ^ j.val %ₘ (cyclotomic 2 ℤ * cyclotomic 4 ℤ) =
      ![1, X, X ^ 2, -X ^ 2 - X - 1] j := by
  apply power_modByMonic_eq_of_certificate
    ((cyclotomic.monic 2 ℤ).mul (cyclotomic.monic 4 ℤ))
  · have hd : (cyclotomic 2 ℤ * cyclotomic 4 ℤ).degree = 3 := by
      rw [cyclotomic_two, cyclotomic_four_int]
      compute_degree!
    rw [hd]
    fin_cases j <;> norm_num
    compute_degree!
  · refine ⟨![0, 0, 0, 1] j, ?_⟩
    rw [cyclotomic_two, cyclotomic_four_int]
    fin_cases j <;> norm_num
    ring

lemma cyclotomic_two_six_power_remainders (j : Fin 6) :
    (X : ℤ[X]) ^ j.val %ₘ (cyclotomic 2 ℤ * cyclotomic 6 ℤ) =
      ![1, X, X ^ 2, -1, -X, -X ^ 2] j := by
  apply power_modByMonic_eq_of_certificate
    ((cyclotomic.monic 2 ℤ).mul (cyclotomic.monic 6 ℤ))
  · have hd : (cyclotomic 2 ℤ * cyclotomic 6 ℤ).degree = 3 := by
      rw [cyclotomic_two, cyclotomic_six]
      compute_degree!
    rw [hd]
    fin_cases j <;> norm_num
  · refine ⟨![0, 0, 0, 1, X, X ^ 2] j, ?_⟩
    rw [cyclotomic_two, cyclotomic_six]
    fin_cases j <;> norm_num <;> ring

end OdlyzkoPoonen
