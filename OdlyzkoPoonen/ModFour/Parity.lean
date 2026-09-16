import OdlyzkoPoonen.Polynomial.Reduction

/-!
# The even autocorrelation difference

For lifts of `a * b` and `a * b.reverse`, the autocorrelations agree modulo two.
Thus every coefficient difference is divisible by two. The half-difference,
reduced modulo two, vanishes exactly when the original difference vanishes
modulo four. Integer division here is justified by the proved evenness.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma lifted_factor_autocorrelation_congruent_two (a b : (ZMod 2)[X])
    (hb : b.coeff 0 ≠ 0) :
    CongruentMod 2 (autocorrelation (zeroOneLift (a * b)))
      (autocorrelation (zeroOneLift (a * b.reverse))) := by
  simp only [CongruentMod, autocorrelation, reducePolynomial_mul,
    ← zeroOneLift_reverse, reduce_zeroOneLift]
  rw [reverse_mul_of_domain, reverse_mul_of_domain,
    reverse_reverse_of_constant_ne_zero hb]
  ring

lemma lifted_factor_autocorrelation_even (a b : (ZMod 2)[X])
    (hb : b.coeff 0 ≠ 0) (k : ℕ) :
    (2 : ℤ) ∣ (autocorrelation (zeroOneLift (a * b))).coeff k -
      (autocorrelation (zeroOneLift (a * b.reverse))).coeff k :=
  (congruentMod_iff_coeff_dvd _ _ _).mp
    (lifted_factor_autocorrelation_congruent_two a b hb) k

lemma four_dvd_iff_two_dvd_half {t : ℤ} (ht : 2 ∣ t) :
    4 ∣ t ↔ 2 ∣ t / 2 := by
  obtain ⟨u, rfl⟩ := ht
  rw [Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
  change 2 * 2 ∣ 2 * u ↔ 2 ∣ u
  exact mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)

/-- The coefficient difference divided in the integers by two and then reduced
modulo two. Its interpretation as a congruence test requires even differences. -/
noncomputable def halfCoefficientDifference (p q : ℤ[X]) (k : ℕ) : ZMod 2 :=
  (((p.coeff k - q.coeff k) / 2 : ℤ) : ZMod 2)

lemma halfCoefficientDifference_eq_zero_iff {p q : ℤ[X]} {k : ℕ}
    (h : (2 : ℤ) ∣ p.coeff k - q.coeff k) :
    halfCoefficientDifference p q k = 0 ↔ (4 : ℤ) ∣ p.coeff k - q.coeff k := by
  rw [halfCoefficientDifference, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact (four_dvd_iff_two_dvd_half h).symm

lemma congruent_four_iff_half_differences_zero {p q : ℤ[X]}
    (h : CongruentMod 2 p q) :
    CongruentMod 4 p q ↔ ∀ k, halfCoefficientDifference p q k = 0 := by
  rw [congruentMod_iff_coeff_dvd]
  have he := (congruentMod_iff_coeff_dvd _ _ _).mp h
  exact forall_congr' (fun k ↦ (halfCoefficientDifference_eq_zero_iff (he k)).symm)

/-- The discrepancy bits in the lifted factor-pair construction. -/
noncomputable def autocorrelationDiscrepancy (a b : (ZMod 2)[X]) (k : ℕ) : ZMod 2 :=
  halfCoefficientDifference (autocorrelation (zeroOneLift (a * b)))
    (autocorrelation (zeroOneLift (a * b.reverse))) k

lemma lifted_factor_congruent_four_iff (a b : (ZMod 2)[X])
    (hb : b.coeff 0 ≠ 0) :
    CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
      (autocorrelation (zeroOneLift (a * b.reverse))) ↔
    ∀ k, autocorrelationDiscrepancy a b k = 0 :=
  congruent_four_iff_half_differences_zero
    (lifted_factor_autocorrelation_congruent_two a b hb)

end OdlyzkoPoonen
