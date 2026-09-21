import OdlyzkoPoonen.Asymptotics.CentralBinomialSecondOrder

/-!
# Central-binomial expansion with a quantified remainder

The first relative correction is `-1/(8*n)`. The finite estimate below follows
from the normalized-square bounds and an elementary difference-of-squares
comparison; no factorial asymptotic is needed.
-/

namespace OdlyzkoPoonen

lemma abs_sub_le_twice_abs_sq_sub_sq {x a : ℝ} (hx : 0 ≤ x) (ha : 1 / 2 ≤ a) :
    |x - a| ≤ 2 * |x ^ 2 - a ^ 2| := by
  have he : |x - a| * (x + a) = |x ^ 2 - a ^ 2| := by
    calc
      _ = |x - a| * |x + a| := by rw [abs_of_nonneg (by linarith : 0 ≤ x + a)]
      _ = |(x - a) * (x + a)| := (abs_mul _ _).symm
      _ = _ := by congr 1; ring
  nlinarith [mul_nonneg (abs_nonneg (x - a)) (show 0 ≤ x + a - 1 / 2 by linarith)]

/-- The central binomial probability with its first correction, and an explicit
remainder of order `n^(-5/2)`. -/
theorem centralBinomialMass_first_correction {n : ℕ} (hn : 1 ≤ n) :
    |centralBinomialMass n - (1 - 1 / (8 * (n : ℝ))) /
        Real.sqrt (Real.pi * (n : ℝ))| ≤
      1 / (2 * (n : ℝ) ^ 2 * Real.sqrt (Real.pi * (n : ℝ))) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let s := Real.sqrt (Real.pi * (n : ℝ))
  let x := s * centralBinomialMass n
  let a := 1 - 1 / (8 * (n : ℝ))
  let e := 1 / (4 * (n : ℝ) ^ 2)
  have hs : 0 < s := by dsimp [s]; positivity
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have hx : 0 ≤ x := mul_nonneg hs.le (centralBinomialMass_pos n).le
  have ha : 1 / 2 ≤ a := by
    have h8 : 1 / (8 * (n : ℝ)) ≤ 1 / 8 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith
    dsimp [a]
    linarith
  have hx2 : x ^ 2 = normalizedCentralBinomialSquare n := by
    dsimp [x, s, normalizedCentralBinomialSquare]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have ha2 : a ^ 2 = 1 - 1 / (4 * (n : ℝ)) + e / 16 := by
    dsimp [a, e]
    field_simp
    ring
  have hl := (normalizedCentralBinomialSquare_correction_bounds hn).1
  have hu := (abs_le.mp (normalizedCentralBinomialSquare_first_correction hn)).2
  have hsq : |x ^ 2 - a ^ 2| ≤ e := by
    rw [hx2, ha2]
    apply abs_le.mpr
    change normalizedCentralBinomialSquare n - (1 - 1 / (4 * (n : ℝ))) ≤ e at hu
    constructor <;> linarith
  have hxa : |x - a| ≤ 2 * e :=
    (abs_sub_le_twice_abs_sq_sub_sq hx ha).trans (by gcongr)
  have he : centralBinomialMass n - a / s = (x - a) / s := by
    dsimp [x]
    field_simp
  change |centralBinomialMass n - a / s| ≤ 1 / (2 * (n : ℝ) ^ 2 * s)
  rw [he, abs_div, abs_of_pos hs]
  calc
    _ ≤ (2 * e) / s := div_le_div_of_nonneg_right hxa hs.le
    _ = _ := by dsimp [e]; ring

/-- The same correction after removing the leading square-root scale. -/
theorem normalizedCentralBinomialMass_first_correction {n : ℕ} (hn : 1 ≤ n) :
    |Real.sqrt (Real.pi * (n : ℝ)) * centralBinomialMass n -
      (1 - 1 / (8 * (n : ℝ)))| ≤ 1 / (2 * (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let s := Real.sqrt (Real.pi * (n : ℝ))
  have hs : 0 < s := by dsimp [s]; positivity
  have h := mul_le_mul_of_nonneg_left (centralBinomialMass_first_correction hn) hs.le
  have he : s * |centralBinomialMass n - (1 - 1 / (8 * (n : ℝ))) / s| =
      |s * centralBinomialMass n - (1 - 1 / (8 * (n : ℝ)))| := by
    calc
      _ = |s| * |centralBinomialMass n - (1 - 1 / (8 * (n : ℝ))) / s| := by
        rw [abs_of_pos hs]
      _ = |s * (centralBinomialMass n - (1 - 1 / (8 * (n : ℝ))) / s)| :=
        (abs_mul _ _).symm
      _ = _ := by congr 1; field_simp
  change s * |centralBinomialMass n - (1 - 1 / (8 * (n : ℝ))) / s| ≤
    s * (1 / (2 * (n : ℝ) ^ 2 * s)) at h
  rw [he] at h
  have hr : s * (1 / (2 * (n : ℝ) ^ 2 * s)) = 1 / (2 * (n : ℝ) ^ 2) := by
    field_simp
  rwa [hr] at h

end OdlyzkoPoonen
