import OdlyzkoPoonen.Probability.CyclotomicResidueBound
import OdlyzkoPoonen.Analysis.AtomScale

/-!
# Probability bounds for fixed divisors of a periodic polynomial

Every divisor of `X^k-1` can be handled by the same residue-block argument.
The probability bound has exponent equal to the divisor's degree, including
when the divisor is a product of distinct cyclotomic polynomials.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics
open scoped BigOperators Classical

lemma periodic_dvd_wordResiduePolynomial_iff {m k : ℕ} {f : ℤ[X]}
    (hperiod : f ∣ X ^ k - 1) (w : Fin m → Bool) :
    f ∣ wordResiduePolynomial k w ↔ f ∣ wordPolynomial w := by
  have hd := dvd_trans hperiod (wordPolynomial_sub_residue_dvd k w)
  constructor
  · intro h
    simpa only [sub_add_cancel] using dvd_add hd h
  · intro h
    simpa only [sub_sub_cancel] using dvd_sub h hd

lemma periodic_dvd_determines_low_residue_coefficients {m k : ℕ} {f : ℤ[X]}
    (hk : 0 < k) (hf : f ≠ 0) (hperiod : f ∣ X ^ k - 1)
    (v w : Fin m → Bool) (hv : f ∣ wordPolynomial v) (hw : f ∣ wordPolynomial w)
    (hhigh : ∀ r : Fin k, f.natDegree ≤ r.val →
      (wordResiduePolynomial k v).coeff r.val = (wordResiduePolynomial k w).coeff r.val) :
    wordResiduePolynomial k v = wordResiduePolynomial k w := by
  apply eq_of_dvd_of_high_coefficients_eq hf
    ((periodic_dvd_wordResiduePolynomial_iff hperiod v).mpr hv)
    ((periodic_dvd_wordResiduePolynomial_iff hperiod w).mpr hw)
  intro i hi
  by_cases hik : i < k
  · exact hhigh ⟨i, hik⟩ hi
  · rw [coeff_wordResiduePolynomial_above hk v (by omega),
      coeff_wordResiduePolynomial_above hk w (by omega)]

/-- A residue-block bound for any fixed divisor of `X^k-1`. -/
theorem binaryProbability_periodic_divisor_bound (m : ℕ) {k : ℕ} {f : ℤ[X]}
    (hk : 0 < k) (hf : f ≠ 0) (hperiod : f ∣ X ^ k - 1) :
    binaryProbability m (fun p ↦ f ∣ p) ≤
      (4 / Real.sqrt (((m : ℝ) + 1) / k)) ^ f.natDegree := by
  classical
  have hdegree : f.natDegree ≤ k := by
    have hz : (X ^ k - 1 : ℤ[X]) ≠ 0 := by
      simpa only [C_1] using X_pow_sub_C_ne_zero (R := ℤ) hk 1
    simpa only [← C_1, natDegree_X_pow_sub_C] using
      natDegree_le_of_dvd hperiod hz
  let α := fun r : Fin k ↦ {i : Fin m // residueIndex hk i = r} → Bool
  let e : (Fin m → Bool) ≃ (∀ r, α r) := groupWordEquiv (residueIndex hk)
  let E := fun w : ∀ r, α r ↦ f ∣ wordPolynomial (e.symm w)
  let c : ℝ := 4 / Real.sqrt (((m : ℝ) + 1) / k)
  have hunique (v w : ∀ r, α r) (hv : E v) (hw : E w)
      (hhigh : ∀ r : Fin k, ¬r.val < f.natDegree → v r = w r) :
      ∀ r : Fin k, r.val < f.natDegree →
        residueBlockCoefficient m hk r (v r) = residueBlockCoefficient m hk r (w r) := by
    have hpoly := periodic_dvd_determines_low_residue_coefficients hk hf hperiod
      (e.symm v) (e.symm w) hv hw (fun r hr ↦ by
        change (wordResiduePolynomial k ((groupWordEquiv (residueIndex hk)).symm v)).coeff r.val =
          (wordResiduePolynomial k ((groupWordEquiv (residueIndex hk)).symm w)).coeff r.val
        rw [coeff_wordResiduePolynomial_grouped, coeff_wordResiduePolynomial_grouped,
          hhigh r (by omega)])
    intro r _
    have heq := congrArg (fun p : ℤ[X] ↦ p.coeff r.val) hpoly
    simpa only [e, coeff_wordResiduePolynomial_grouped] using heq
  calc
    _ = uniformProbability E := by
      exact (uniformProbability_equiv e.symm
        (fun w : Fin m → Bool ↦ f ∣ wordPolynomial w)).symm
    _ ≤ ∏ r : {r : Fin k // r.val < f.natDegree}, c := by
      convert uniformProbability_selected_coordinates_le
        (fun r : Fin k ↦ r.val < f.natDegree) E
        (fun r ↦ residueBlockCoefficient m hk r) (fun _ ↦ c)
        (fun _ _ ↦ by dsimp [c]; positivity)
        (fun r _ z ↦ uniformProbability_residueBlockCoefficient_le m hk r z) hunique using 1
      congr 2
      exact Subsingleton.elim _ _
    _ = _ := by
      let er : {r : Fin k // r.val < f.natDegree} ≃ Fin f.natDegree :=
        { toFun := fun r ↦ ⟨r.val.val, r.property⟩
          invFun := fun r ↦ ⟨⟨r.val, lt_of_lt_of_le r.isLt hdegree⟩, r.isLt⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_congr er, Fintype.card_fin]

lemma binaryProbability_periodic_divisor_bound_degree {n k : ℕ} {f : ℤ[X]}
    (hn : 1 ≤ n) (hk : 0 < k) (hf : f ≠ 0) (hperiod : f ∣ X ^ k - 1) :
    binaryProbability (n - 1) (fun p ↦ f ∣ p) ≤
      (4 / Real.sqrt ((n : ℝ) / k)) ^ f.natDegree := by
  have hnR : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel hn
  simpa only [hnR] using binaryProbability_periodic_divisor_bound (n - 1) hk hf hperiod

/-- Each two degrees of a fixed periodic divisor give one inverse power. -/
theorem binaryProbability_periodic_divisor_isBigO {k R : ℕ} {f : ℤ[X]}
    (hk : 0 < k) (hf : f ≠ 0) (hperiod : f ∣ X ^ k - 1)
    (hdegree : 2 * R ≤ f.natDegree) :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ f ∣ p)) =O[atTop]
      (fun n : ℕ ↦ ((n : ℝ) ^ R)⁻¹) := by
  refine isBigO_iff.mpr ⟨(16 * (k : ℝ)) ^ R, ?_⟩
  filter_upwards [eventually_ge_atTop (16 * k)] with n hn
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hscale : 4 / Real.sqrt ((n : ℝ) / k) ≤ 1 := by
    have hnk : 16 * (k : ℝ) ≤ n := by exact_mod_cast hn
    have he := residue_atom_scale_sq hn0 hk0
    have hb : 16 * (k : ℝ) / n ≤ 1 := (div_le_one hn0).mpr hnk
    nlinarith [show 0 ≤ 4 / Real.sqrt ((n : ℝ) / k) by positivity]
  have hp0 : 0 ≤ binaryProbability (n - 1) (fun p ↦ f ∣ p) := uniformProbability_nonneg _
  simp only [Real.norm_eq_abs, abs_of_nonneg hp0,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hn0.le R))]
  calc
    _ ≤ (4 / Real.sqrt ((n : ℝ) / k)) ^ f.natDegree :=
      binaryProbability_periodic_divisor_bound_degree hn1 hk hf hperiod
    _ ≤ (4 / Real.sqrt ((n : ℝ) / k)) ^ (2 * R) :=
      pow_le_pow_of_le_one (by positivity) hscale hdegree
    _ = _ := by rw [pow_mul, residue_atom_scale_sq hn0 hk0, div_pow, div_eq_mul_inv]

end OdlyzkoPoonen
