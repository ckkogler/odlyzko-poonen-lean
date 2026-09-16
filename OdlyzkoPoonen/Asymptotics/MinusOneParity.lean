import OdlyzkoPoonen.Asymptotics.MinusOneMass
import OdlyzkoPoonen.Analysis.SquareRootComparison

/-!
# Uniform error bounds for the two degree parities

The exact even-degree correction and the central Wallis estimate give a common
bound `3/(r*sqrt r)` for both parity errors. The parameter is half the degree;
passing to every original degree is performed separately.
-/

namespace OdlyzkoPoonen

lemma binaryProbability_minus_one_even_error {r : ℕ} (hr : 1 ≤ r) :
    |binaryProbability (2 * r - 1) (fun p ↦ p.eval (-1) = 0) -
      Real.sqrt (2 / (Real.pi * (2 * (r : ℝ))))| ≤
        3 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  let c := centralBinomialMass r
  let t := 1 / Real.sqrt (Real.pi * (r : ℝ))
  let a := ((r : ℝ) - 1) / ((r : ℝ) + 1)
  have hc : 0 ≤ c := (centralBinomialMass_pos r).le
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hct : c ≤ t := centralBinomialMass_le_sqrt hr
  have herror : t - c ≤ t / (2 * (r : ℝ) + 1) := by
    have h := centralBinomialMass_abs_sub_sqrt_le hr
    change |c - t| ≤ t / (2 * (r : ℝ) + 1) at h
    rw [abs_of_nonpos (sub_nonpos.mpr hct)] at h
    linarith
  have ha1 : a ≤ 1 := by
    dsimp [a]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hac : a * c ≤ c := by
    have h := mul_le_mul_of_nonneg_right ha1 hc
    simpa only [one_mul] using h
  have ha : 1 - a = 2 / ((r : ℝ) + 1) := by
    dsimp [a]
    field_simp
    ring
  have hd : t - a * c ≤ t / (2 * (r : ℝ) + 1) + 2 / ((r : ℝ) + 1) * t := by
    calc
      t - a * c = (t - c) + (1 - a) * c := by ring
      _ = (t - c) + 2 / ((r : ℝ) + 1) * c := by rw [ha]
      _ ≤ t / (2 * (r : ℝ) + 1) + 2 / ((r : ℝ) + 1) * t :=
        add_le_add herror (mul_le_mul_of_nonneg_left hct (by positivity))
  have hd1 : t / (2 * (r : ℝ) + 1) ≤ t / (r : ℝ) :=
    div_le_div_of_nonneg_left ht hr0 (by linarith)
  have hd2 : 2 / ((r : ℝ) + 1) * t ≤ 2 * (t / (r : ℝ)) := by
    calc
      2 / ((r : ℝ) + 1) * t = (2 * t) / ((r : ℝ) + 1) := by ring
      _ ≤ (2 * t) / (r : ℝ) := div_le_div_of_nonneg_left (by positivity) hr0 (by linarith)
      _ = 2 * (t / (r : ℝ)) := by ring
  have hdt : t - a * c ≤ 3 * t / (r : ℝ) := by
    calc
      t - a * c ≤ t / (2 * (r : ℝ) + 1) + 2 / ((r : ℝ) + 1) * t := hd
      _ ≤ t / (r : ℝ) + 2 * (t / (r : ℝ)) := add_le_add hd1 hd2
      _ = 3 * t / (r : ℝ) := by ring
  have ht' : t ≤ 1 / Real.sqrt (r : ℝ) := inverse_sqrt_pi_le hr0
  have hbound : 3 * t / (r : ℝ) ≤ 3 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by
    calc
      3 * t / (r : ℝ) ≤ 3 * (1 / Real.sqrt (r : ℝ)) / (r : ℝ) := by gcongr
      _ = 3 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by ring
  rw [binaryProbability_minus_one_even_eq_central hr, sqrt_two_div_double]
  change |a * c - t| ≤ _
  rw [abs_of_nonpos (sub_nonpos.mpr (hac.trans hct))]
  linarith

lemma binaryProbability_minus_one_odd_error {r : ℕ} (hr : 1 ≤ r) :
    |binaryProbability (2 * r) (fun p ↦ p.eval (-1) = 0) -
      Real.sqrt (2 / (Real.pi * (2 * (r : ℝ) + 1)))| ≤
        3 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by
  have hr0 : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  let c := centralBinomialMass r
  let t := 1 / Real.sqrt (Real.pi * (r : ℝ))
  let u := Real.sqrt (2 / (Real.pi * (2 * (r : ℝ) + 1)))
  have huc : u ≤ c := by
    have h := Real.sqrt_le_sqrt (centralBinomialMass_sq_lower r)
    simpa [Real.sqrt_sq (centralBinomialMass_pos r).le, u, c] using h
  have hct : c ≤ t := centralBinomialMass_le_sqrt hr
  have htu : t - u ≤ t / (2 * (r : ℝ) + 1) := (sqrt_odd_degree_comparison hr0).2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht' : t ≤ 1 / Real.sqrt (r : ℝ) := inverse_sqrt_pi_le hr0
  have hd : t / (2 * (r : ℝ) + 1) ≤ 3 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by
    calc
      t / (2 * (r : ℝ) + 1) ≤ t / (r : ℝ) :=
        div_le_div_of_nonneg_left ht hr0 (by linarith)
      _ ≤ (1 / Real.sqrt (r : ℝ)) / (r : ℝ) := by gcongr
      _ = 1 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by ring
      _ ≤ 3 / ((r : ℝ) * Real.sqrt (r : ℝ)) := by gcongr; norm_num
  rw [binaryProbability_minus_one_odd_eq_central]
  change |c - u| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr huc)]
  linarith

end OdlyzkoPoonen
