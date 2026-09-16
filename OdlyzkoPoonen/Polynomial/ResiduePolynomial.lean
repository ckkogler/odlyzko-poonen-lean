import OdlyzkoPoonen.Polynomial.BinaryWords
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Collecting exponents modulo a cyclotomic order

Replacing every exponent by its residue modulo `k` changes a polynomial by a
multiple of `X^k-1`, hence by a multiple of the `k`th cyclotomic polynomial.
For a binary word the coefficient in a residue class is the sum of its free
bits plus the two deterministic endpoint contributions.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma X_pow_sub_one_dvd_pow_sub_residue (k n : ℕ) :
    (X ^ k - 1 : ℤ[X]) ∣ X ^ n - X ^ (n % k) := by
  have h : (X ^ k - 1 : ℤ[X]) ∣ (X ^ k) ^ (n / k) - 1 := by
    simpa only [one_pow] using sub_dvd_pow_sub_pow (X ^ k : ℤ[X]) 1 (n / k)
  have he : (X ^ (n % k) : ℤ[X]) * ((X ^ k) ^ (n / k) - 1) =
      X ^ n - X ^ (n % k) := by
    rw [mul_sub, mul_one, ← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [← he]
  exact dvd_mul_of_dvd_right h _

/-- The binary polynomial with all exponents reduced modulo `k`. -/
noncomputable def wordResiduePolynomial {m : ℕ} (k : ℕ) (w : Fin m → Bool) : ℤ[X] :=
  1 + (∑ i, C (bitValue (w i)) * X ^ ((i.val + 1) % k)) + X ^ ((m + 1) % k)

lemma wordPolynomial_sub_residue_dvd {m : ℕ} (k : ℕ) (w : Fin m → Bool) :
    (X ^ k - 1 : ℤ[X]) ∣ wordPolynomial w - wordResiduePolynomial k w := by
  have he : wordPolynomial w - wordResiduePolynomial k w =
      (∑ i : Fin m, C (bitValue (w i)) *
        (X ^ (i.val + 1) - X ^ ((i.val + 1) % k))) +
        (X ^ (m + 1) - X ^ ((m + 1) % k)) := by
    simp only [wordPolynomial, interiorPolynomial, wordResiduePolynomial, mul_sub,
      Finset.sum_sub_distrib]
    ring
  rw [he]
  apply dvd_add
  · exact Finset.dvd_sum (fun i _ ↦ dvd_mul_of_dvd_right
      (X_pow_sub_one_dvd_pow_sub_residue k (i.val + 1)) _)
  · exact X_pow_sub_one_dvd_pow_sub_residue k (m + 1)

lemma cyclotomic_dvd_wordResiduePolynomial_iff {m : ℕ} (k : ℕ) (w : Fin m → Bool) :
    cyclotomic k ℤ ∣ wordResiduePolynomial k w ↔ cyclotomic k ℤ ∣ wordPolynomial w := by
  have hd := dvd_trans (cyclotomic.dvd_X_pow_sub_one k ℤ)
    (wordPolynomial_sub_residue_dvd k w)
  constructor
  · intro h
    simpa only [sub_add_cancel] using dvd_add hd h
  · intro h
    simpa only [sub_sub_cancel] using dvd_sub h hd

/-- The constant and leading endpoint contributions to a residue coefficient. -/
def residueEndpointShift (m k r : ℕ) : ℤ :=
  (if r = 0 then 1 else 0) + (if r = (m + 1) % k then 1 else 0)

lemma coeff_wordResiduePolynomial {m : ℕ} (k : ℕ) (w : Fin m → Bool) (r : ℕ) :
    (wordResiduePolynomial k w).coeff r = residueEndpointShift m k r +
      ∑ i : {i : Fin m // (i.val + 1) % k = r}, bitValue (w i.val) := by
  have hs : (∑ i : Fin m, bitValue (w i) * (if r = (i.val + 1) % k then 1 else 0)) =
      ∑ i : {i : Fin m // (i.val + 1) % k = r}, bitValue (w i.val) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp [eq_comm]) _
  simp only [wordResiduePolynomial, coeff_add, finsetSum_coeff, coeff_C_mul,
    coeff_X_pow, coeff_one, hs, residueEndpointShift]
  ring

lemma coeff_wordResiduePolynomial_above {m k : ℕ} (hk : 0 < k)
    (w : Fin m → Bool) {r : ℕ} (hr : k ≤ r) :
    (wordResiduePolynomial k w).coeff r = 0 := by
  have hr0 : r ≠ 0 := by omega
  have ht : r ≠ (m + 1) % k := by have := Nat.mod_lt (m + 1) hk; omega
  have hi (i : Fin m) : r ≠ (i.val + 1) % k := by
    have := Nat.mod_lt (i.val + 1) hk
    omega
  simp [wordResiduePolynomial, coeff_add, finsetSum_coeff, coeff_C_mul,
    coeff_X_pow, coeff_one, hr0, ht, hi]

end OdlyzkoPoonen
