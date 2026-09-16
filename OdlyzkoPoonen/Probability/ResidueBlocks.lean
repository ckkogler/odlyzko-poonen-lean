import OdlyzkoPoonen.Probability.WordGrouping
import OdlyzkoPoonen.Probability.FiniteBitSums
import OdlyzkoPoonen.Arithmetic.ResidueClassSize
import OdlyzkoPoonen.Polynomial.ResiduePolynomial
import OdlyzkoPoonen.Polynomial.DivisorCoefficientUniqueness

/-!
# Independent residue blocks of binary coefficients

The grouping map records the residue of each actual internal exponent. The
associated integer statistic includes both endpoint contributions. Its law is
a shifted fair-bit sum, with a bound uniform in the target and the residue.
Cyclotomic divisibility determines the low residue coefficients once the high
ones are fixed.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

/-- The residue of the exponent occupied by a free coefficient. -/
def residueIndex {m k : ℕ} (hk : 0 < k) (i : Fin m) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩

/-- The fiber of the finite-valued index has the same elements as the residue class. -/
def residueFiberEquiv (m : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k) :
    {i : Fin m // residueIndex hk i = r} ≃ {i : Fin m // (i.val + 1) % k = r.val} where
  toFun i := ⟨i.val, congrArg Fin.val i.property⟩
  invFun i := ⟨i.val, Fin.ext i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The whole coefficient of a residue polynomial, including its endpoints. -/
noncomputable def residueBlockCoefficient (m : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k)
    (w : {i : Fin m // residueIndex hk i = r} → Bool) : ℤ :=
  residueEndpointShift m k r.val + ∑ i, bitValue (w i)

lemma coeff_wordResiduePolynomial_eq_block {m k : ℕ} (hk : 0 < k)
    (w : Fin m → Bool) (r : Fin k) :
    (wordResiduePolynomial k w).coeff r.val =
      residueBlockCoefficient m hk r (groupWordEquiv (residueIndex hk) w r) := by
  rw [coeff_wordResiduePolynomial]
  unfold residueBlockCoefficient
  congr 1
  exact ((residueFiberEquiv m hk r).sum_comp (fun i ↦ bitValue (w i.val))).symm

lemma coeff_wordResiduePolynomial_grouped {m k : ℕ} (hk : 0 < k)
    (w : ∀ r : Fin k, {i : Fin m // residueIndex hk i = r} → Bool) (r : Fin k) :
    (wordResiduePolynomial k ((groupWordEquiv (residueIndex hk)).symm w)).coeff r.val =
      residueBlockCoefficient m hk r (w r) := by
  simpa only [Equiv.apply_symm_apply] using
    coeff_wordResiduePolynomial_eq_block hk ((groupWordEquiv (residueIndex hk)).symm w) r

lemma card_residueIndex_fiber_add_one_ge (m : ℕ) {k : ℕ} (hk : 0 < k) (r : Fin k) :
    (m + 1 : ℝ) / k ≤
      (Fintype.card {i : Fin m // residueIndex hk i = r} : ℝ) + 1 := by
  rw [Fintype.card_congr (residueFiberEquiv m hk r)]
  exact card_positive_residue_class_add_one_ge m hk r

lemma uniformProbability_residueBlockCoefficient_le (m : ℕ) {k : ℕ}
    (hk : 0 < k) (r : Fin k) (z : ℤ) :
    uniformProbability (fun w ↦ residueBlockCoefficient m hk r w = z) ≤
      4 / Real.sqrt (((m : ℝ) + 1) / k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    _ ≤ 4 / Real.sqrt ((Fintype.card {i : Fin m // residueIndex hk i = r} : ℝ) + 1) :=
      uniformProbability_finite_bit_sum_le (residueEndpointShift m k r.val) z
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact Real.sqrt_le_sqrt (card_residueIndex_fiber_add_one_ge m hk r)

lemma cyclotomic_dvd_determines_low_residue_coefficients {m k : ℕ} (hk : 0 < k)
    (v w : Fin m → Bool) (hv : cyclotomic k ℤ ∣ wordPolynomial v)
    (hw : cyclotomic k ℤ ∣ wordPolynomial w)
    (hhigh : ∀ r : Fin k, k.totient ≤ r.val →
      (wordResiduePolynomial k v).coeff r.val = (wordResiduePolynomial k w).coeff r.val) :
    wordResiduePolynomial k v = wordResiduePolynomial k w := by
  apply eq_of_dvd_of_high_coefficients_eq (cyclotomic.monic k ℤ).ne_zero
    ((cyclotomic_dvd_wordResiduePolynomial_iff k v).mpr hv)
    ((cyclotomic_dvd_wordResiduePolynomial_iff k w).mpr hw)
  intro i hi
  rw [natDegree_cyclotomic] at hi
  by_cases hik : i < k
  · exact hhigh ⟨i, hik⟩ hi
  · rw [coeff_wordResiduePolynomial_above hk v (by omega),
      coeff_wordResiduePolynomial_above hk w (by omega)]

end OdlyzkoPoonen
