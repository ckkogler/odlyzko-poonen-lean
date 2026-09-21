import OdlyzkoPoonen.Polynomial.ResidueWordDifference
import OdlyzkoPoonen.Polynomial.SparseDivisorUniqueness
import OdlyzkoPoonen.Polynomial.RationalSeparable

/-!
# Uniqueness when only one residue class can change

A shift moves the allowed coefficients to multiples of `q`. Separated root
powers and the Mahler lower bound then rule out any nonzero difference between
two binary samples divisible by the same monic polynomial.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma word_eq_of_residue_divisibility {m q a : ℕ} (hq : 0 < q) (ha : a < q)
    {J : ℤ[X]} (hJ : J.Monic)
    (hsimple : (J.map (Int.castRingHom ℂ)).roots.Nodup)
    (hsep : ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ w ∈ (J.map (Int.castRingHom ℂ)).roots, z ^ q = w ^ q → z = w)
    (hlarge : Real.sqrt ((m + q + 1 : ℕ) : ℝ) <
      (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ q)
    (v w : Fin m → Bool) (hv : J ∣ wordPolynomial v) (hw : J ∣ wordPolynomial w)
    (hfixed : ∀ i : Fin m, (i.val + 1) % q ≠ a → v i = w i) : v = w := by
  by_contra hne
  let R := contract q (X ^ (q - a) * (wordPolynomial v - wordPolynomial w))
  have he : expand ℤ q R = X ^ (q - a) * (wordPolynomial v - wordPolynomial w) :=
    residue_word_difference_expand hq ha v w hfixed
  have hR : R ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at he
    have hd : wordPolynomial v - wordPolynomial w = 0 :=
      (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ X_ne_zero)
    exact hne (wordPolynomial_injective (sub_eq_zero.mp hd))
  have hd : J ∣ expand ℤ q R := by
    rw [he]
    exact dvd_mul_of_dvd_right (dvd_sub hv hw) _
  have hmap : J.map (Int.castRingHom ℂ) ∣ expand ℂ q (R.map (Int.castRingHom ℂ)) := by
    simpa only [map_expand] using Polynomial.map_dvd (Int.castRingHom ℂ) hd
  have hlow := mahlerMeasure_pow_le_of_dvd_expand q (hJ.map _)
    (one_le_norm_leadingCoeff_int_map hR) hsimple hsep hmap
  have hupp := mahlerMeasure_contract_shifted_word_difference_le
    hq (Nat.sub_le q a) v w
  exact (not_lt_of_ge (hlow.trans hupp)) hlarge

lemma word_eq_of_rational_irreducible_residue_divisibility {m q a : ℕ}
    (hq : 0 < q) (ha : a < q) {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ)))
    (hsep : ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ w ∈ (J.map (Int.castRingHom ℂ)).roots, z ^ q = w ^ q → z = w)
    (hlarge : Real.sqrt ((m + q + 1 : ℕ) : ℝ) <
      (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ q)
    (v w : Fin m → Bool) (hv : J ∣ wordPolynomial v) (hw : J ∣ wordPolynomial w)
    (hfixed : ∀ i : Fin m, (i.val + 1) % q ≠ a → v i = w i) : v = w :=
  word_eq_of_residue_divisibility hq ha hJ
    (complex_roots_nodup_of_rational_irreducible hirr) hsep hlarge v w hv hw hfixed

end OdlyzkoPoonen
