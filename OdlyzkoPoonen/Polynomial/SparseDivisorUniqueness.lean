import OdlyzkoPoonen.Analysis.IntegerMahlerMeasure
import OdlyzkoPoonen.Analysis.MahlerRootPowers
import OdlyzkoPoonen.Polynomial.ContractedBinaryDifference

/-!
# Uniqueness after fixing the nonsparse bits

If `M(J)^q` exceeds the coefficient bound and the `q`th powers of its roots
are distinct, two binary samples divisible by `J` cannot differ only at
multiples of `q`. A nonzero difference would contradict the proved lower
root-product bound and upper coefficient bound for its contraction.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma word_eq_of_sparse_divisibility {m q : ℕ} (hq : 0 < q) {J : ℤ[X]}
    (hJ : J.Monic) (hsimple : (J.map (Int.castRingHom ℂ)).roots.Nodup)
    (hsep : ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ w ∈ (J.map (Int.castRingHom ℂ)).roots, z ^ q = w ^ q → z = w)
    (hlarge : Real.sqrt ((m / q : ℕ) : ℝ) <
      (J.map (Int.castRingHom ℂ)).mahlerMeasure ^ q)
    (v w : Fin m → Bool) (hv : J ∣ wordPolynomial v) (hw : J ∣ wordPolynomial w)
    (hfixed : ∀ i : Fin m, ¬ q ∣ i.val + 1 → v i = w i) : v = w := by
  by_contra hne
  let R := contract q (wordPolynomial v - wordPolynomial w)
  have hR : R ≠ 0 := sparse_word_difference_contract_ne_zero hq v w hfixed hne
  have hd : J ∣ expand ℤ q R := by
    rw [sparse_word_difference_expand hq v w hfixed]
    exact dvd_sub hv hw
  have hmap : J.map (Int.castRingHom ℂ) ∣ expand ℂ q (R.map (Int.castRingHom ℂ)) := by
    simpa only [map_expand] using Polynomial.map_dvd (Int.castRingHom ℂ) hd
  have hlow := mahlerMeasure_pow_le_of_dvd_expand q (hJ.map _)
    (one_le_norm_leadingCoeff_int_map hR) hsimple hsep hmap
  have hupp := mahlerMeasure_contract_word_difference_le hq v w
  exact (not_lt_of_ge (hlow.trans hupp)) hlarge

end OdlyzkoPoonen
