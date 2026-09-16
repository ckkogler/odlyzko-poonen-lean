import OdlyzkoPoonen.Polynomial.ComplexRootPowerPrime

/-!
# A uniform logarithmic threshold for a separating prime

One absolute constant works for every monic irreducible integer polynomial
with nonzero constant coefficient. At any real scale above that constant times
`1 + log degree`, a prime between the scale and sixteen times the scale makes
the powers of all distinct complex roots distinct. No Mahler-measure lower
bound is assumed in this geometric/arithmetic input.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma exists_uniform_logarithmic_root_power_prime :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℤ[X], J.Monic →
      Irreducible (J.map (Int.castRingHom ℚ)) → J.coeff 0 ≠ 0 →
      ∀ s : ℝ, C * (1 + Real.log (J.natDegree : ℝ)) ≤ s →
      ∃ p : ℕ, p.Prime ∧ s < (p : ℝ) ∧ (p : ℝ) ≤ 16 * s ∧
        ∀ z ∈ (J.map (Int.castRingHom ℂ)).roots,
        ∀ w ∈ (J.map (Int.castRingHom ℂ)).roots, z ^ p = w ^ p → z = w := by
  obtain ⟨n₀, hn₀, hgrowth⟩ := exists_threshold_exp_le_primeIntervalProduct
  refine ⟨max 5 (n₀ : ℝ), by positivity, ?_⟩
  intro J hmonic hirr hconst s hs
  have hdegree : 0 < J.natDegree := by
    have h := hirr.natDegree_pos
    rw [natDegree_map_eq_of_injective (Int.cast_injective : Function.Injective
      (Int.castRingHom ℚ))] at h
    exact h
  have hd : (0 : ℝ) < (J.natDegree : ℝ) := Nat.cast_pos.mpr hdegree
  have hlogd : 0 ≤ Real.log (J.natDegree : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hdegree)
  have hC : (5 : ℝ) ≤ max 5 (n₀ : ℝ) := le_max_left _ _
  have hN : (n₀ : ℝ) ≤ max 5 (n₀ : ℝ) := le_max_right _ _
  have hsC : max 5 (n₀ : ℝ) ≤ s := by nlinarith
  have hs1 : 1 ≤ s := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hceil : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
  have hn : n₀ ≤ ⌈s⌉₊ := by exact_mod_cast hN.trans (hsC.trans hceil)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog : Real.log (2 * (J.natDegree : ℝ) ^ 4) < (⌈s⌉₊ : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hd.ne'), Real.log_pow]
    norm_num
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (by linarith : 0 ≤ 1 + Real.log (J.natDegree : ℝ))]
  obtain ⟨p, hp, hnp, hpn, hsep⟩ :=
    exists_prime_separating_integer_polynomial_roots_of_log_lt
      hmonic hirr hconst (hgrowth _ hn) hlog
  refine ⟨p, hp, hceil.trans_lt (by exact_mod_cast hnp), ?_, hsep⟩
  have hceilupper := Nat.ceil_lt_add_one hs0
  have hpn' : (p : ℝ) ≤ 8 * (⌈s⌉₊ : ℝ) := by exact_mod_cast hpn
  nlinarith

end OdlyzkoPoonen
