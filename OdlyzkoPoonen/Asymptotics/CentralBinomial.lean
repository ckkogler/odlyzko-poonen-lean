import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-!
# Quantitative estimates for the central binomial probability

The normalized central coefficient is linked exactly to the finite Wallis
product. The two proved Wallis inequalities give explicit bounds; no asymptotic
formula for the factorial is assumed.
-/

namespace OdlyzkoPoonen
open scoped Nat

/-- The probability of exactly half true bits in a word of length `2*n`. -/
noncomputable def centralBinomialMass (n : ℕ) : ℝ :=
  (Nat.centralBinom n : ℝ) / 4 ^ n

lemma centralBinomialMass_pos (n : ℕ) : 0 < centralBinomialMass n := by
  unfold centralBinomialMass
  exact div_pos (Nat.cast_pos.mpr (Nat.centralBinom_pos n)) (by positivity)

lemma centralBinomialMass_eq_choose (n : ℕ) :
    centralBinomialMass n = ((2 * n).choose n : ℝ) / (2 : ℝ) ^ (2 * n) := by
  rw [centralBinomialMass, Nat.centralBinom_eq_two_mul_choose, pow_mul]
  norm_num

lemma centralBinomialMass_wallis_identity (n : ℕ) :
    Real.Wallis.W n * ((2 * (n : ℝ) + 1) * centralBinomialMass n ^ 2) = 1 := by
  have hf : (Nat.centralBinom n : ℝ) * (n ! : ℝ) ^ 2 = ((2 * n)! : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    have hn : 2 * n - n = n := by omega
    rw [hn, ← Nat.centralBinom_eq_two_mul_choose] at h
    exact_mod_cast (by simpa [pow_two, mul_assoc] using h :
      Nat.centralBinom n * n ! ^ 2 = (2 * n)!)
  have hp : (2 : ℝ) ^ (4 * n) = (4 ^ n) ^ 2 := by
    calc
      (2 : ℝ) ^ (4 * n) = ((2 : ℝ) ^ 4) ^ n := pow_mul _ _ _
      _ = ((4 : ℝ) ^ 2) ^ n := by norm_num
      _ = ((4 : ℝ) ^ n) ^ 2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 n]
  rw [Real.Wallis.W_eq_factorial_ratio, ← hf, hp, centralBinomialMass]
  have hc : (Nat.centralBinom n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.centralBinom_ne_zero n)
  have hfact : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

lemma centralBinomialMass_sq_lower (n : ℕ) :
    2 / (Real.pi * (2 * (n : ℝ) + 1)) ≤ centralBinomialMass n ^ 2 := by
  have hw := Real.Wallis.W_le n
  have hi := centralBinomialMass_wallis_identity n
  have hmul := mul_le_mul_of_nonneg_right hw
    (show 0 ≤ (2 * (n : ℝ) + 1) * centralBinomialMass n ^ 2 by positivity)
  rw [hi] at hmul
  apply (div_le_iff₀ (by positivity : 0 < Real.pi * (2 * (n : ℝ) + 1))).mpr
  nlinarith

lemma centralBinomialMass_sq_upper_aux (n : ℕ) :
    Real.pi * (2 * (n : ℝ) + 1) ^ 2 * centralBinomialMass n ^ 2 ≤
      4 * ((n : ℝ) + 1) := by
  have hw := Real.Wallis.le_W n
  have hi := centralBinomialMass_wallis_identity n
  have hmul := mul_le_mul_of_nonneg_right hw
    (show 0 ≤ (2 * (n : ℝ) + 1) * centralBinomialMass n ^ 2 by positivity)
  rw [hi] at hmul
  have hn : 0 < 2 * (n : ℝ) + 2 := by positivity
  have h : Real.pi * (2 * (n : ℝ) + 1) ^ 2 * centralBinomialMass n ^ 2 /
      (2 * (2 * (n : ℝ) + 2)) ≤ 1 := by
    convert hmul using 1 <;> field_simp <;> ring
  have hh := (div_le_one (by positivity : 0 < 2 * (2 * (n : ℝ) + 2))).mp h
  nlinarith

lemma centralBinomialMass_sq_upper {n : ℕ} (hn : 1 ≤ n) :
    centralBinomialMass n ^ 2 ≤ 1 / (Real.pi * (n : ℝ)) := by
  have hu := centralBinomialMass_sq_upper_aux n
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  apply (le_div_iff₀ (mul_pos Real.pi_pos hn0)).mpr
  have hc : 0 ≤ Real.pi * centralBinomialMass n ^ 2 := by positivity
  have h : 4 * ((n : ℝ) + 1) *
      (centralBinomialMass n ^ 2 * (Real.pi * (n : ℝ))) ≤
      4 * ((n : ℝ) + 1) * 1 := by nlinarith
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * ((n : ℝ) + 1))).mp h

lemma centralBinomialMass_le_sqrt {n : ℕ} (hn : 1 ≤ n) :
    centralBinomialMass n ≤ 1 / Real.sqrt (Real.pi * (n : ℝ)) := by
  have h := Real.sqrt_le_sqrt (centralBinomialMass_sq_upper hn)
  simpa [Real.sqrt_sq (centralBinomialMass_pos n).le, Real.sqrt_div] using h

/-- An explicit error bound of order `n^(-3/2)` for the normalized central coefficient. -/
lemma centralBinomialMass_abs_sub_sqrt_le {n : ℕ} (hn : 1 ≤ n) :
    |centralBinomialMass n - 1 / Real.sqrt (Real.pi * (n : ℝ))| ≤
      (1 / Real.sqrt (Real.pi * (n : ℝ))) / (2 * (n : ℝ) + 1) := by
  let t : ℝ := 1 / Real.sqrt (Real.pi * (n : ℝ))
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hn0
  have ht : 0 < t := by dsimp [t]; positivity
  have ht2 : t ^ 2 = 1 / (Real.pi * (n : ℝ)) := by
    dsimp [t]
    rw [div_pow, Real.sq_sqrt hp.le, one_pow]
  have hu : centralBinomialMass n ≤ t := centralBinomialMass_le_sqrt hn
  have hl := centralBinomialMass_sq_lower n
  have hi : t ^ 2 - 2 / (Real.pi * (2 * (n : ℝ) + 1)) =
      t ^ 2 / (2 * (n : ℝ) + 1) := by
    rw [ht2]
    field_simp
    ring
  have hs : t ^ 2 - centralBinomialMass n ^ 2 ≤ t ^ 2 / (2 * (n : ℝ) + 1) := by
    rw [← hi]
    linarith
  have hmul : t * (t - centralBinomialMass n) ≤ t ^ 2 / (2 * (n : ℝ) + 1) := by
    nlinarith [mul_nonneg (centralBinomialMass_pos n).le (sub_nonneg.mpr hu)]
  have he : t ^ 2 / (2 * (n : ℝ) + 1) = t * (t / (2 * (n : ℝ) + 1)) := by ring
  rw [he] at hmul
  have hd := (mul_le_mul_iff_right₀ ht).mp hmul
  change |centralBinomialMass n - t| ≤ t / (2 * (n : ℝ) + 1)
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith

end OdlyzkoPoonen
