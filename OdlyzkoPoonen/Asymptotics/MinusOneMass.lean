import OdlyzkoPoonen.Asymptotics.CentralBinomial
import OdlyzkoPoonen.Probability.MinusOne

/-!
# Expressing both parity laws using the central binomial mass

For odd degree the probability is the central mass itself. For even degree
`2*r` it is multiplied by `(r-1)/(r+1)`. This exact correction, including
`r=1`, permits a quantitative asymptotic comparison with a common leading term.
-/

namespace OdlyzkoPoonen

lemma adjacent_even_choose_identity {r : ℕ} (hr : 1 ≤ r) :
    2 * ((r : ℝ) + 1) * ((2 * r - 1).choose (r + 1) : ℝ) =
      ((r : ℝ) - 1) * ((2 * r).choose r : ℝ) := by
  have he : 2 * r - 1 + 1 = 2 * r := by omega
  have hd : 2 * r - 1 - r = r - 1 := by omega
  have hd' : 2 * r - r = r := by omega
  have h₁ := Nat.choose_mul_succ_eq (2 * r - 1) r
  rw [he, hd'] at h₁
  have h₂ := Nat.choose_succ_right_eq (2 * r - 1) r
  rw [hd] at h₂
  have h₁' : ((2 * r - 1).choose r : ℝ) * (2 * (r : ℝ)) =
      ((2 * r).choose r : ℝ) * (r : ℝ) := by exact_mod_cast h₁
  have h₂' : ((2 * r - 1).choose (r + 1) : ℝ) * ((r : ℝ) + 1) =
      ((2 * r - 1).choose r : ℝ) * ((r : ℝ) - 1) := by
    have hc : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub hr]
      norm_num
    have h := congrArg (fun n : ℕ ↦ (n : ℝ)) h₂
    push_cast at h
    rwa [hc] at h
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  apply (mul_left_cancel₀ hr0)
  calc
    (r : ℝ) * (2 * ((r : ℝ) + 1) * ((2 * r - 1).choose (r + 1) : ℝ)) =
        (2 * (r : ℝ)) * (((2 * r - 1).choose (r + 1) : ℝ) * ((r : ℝ) + 1)) := by ring
    _ = (2 * (r : ℝ)) * (((2 * r - 1).choose r : ℝ) * ((r : ℝ) - 1)) := by rw [h₂']
    _ = (((2 * r - 1).choose r : ℝ) * (2 * (r : ℝ))) * ((r : ℝ) - 1) := by ring
    _ = (((2 * r).choose r : ℝ) * (r : ℝ)) * ((r : ℝ) - 1) := by rw [h₁']
    _ = (r : ℝ) * (((r : ℝ) - 1) * ((2 * r).choose r : ℝ)) := by ring

lemma binaryProbability_minus_one_odd_eq_central (r : ℕ) :
    binaryProbability (2 * r) (fun p ↦ p.eval (-1) = 0) = centralBinomialMass r := by
  rw [binaryProbability_minus_one_odd, centralBinomialMass_eq_choose]

lemma binaryProbability_minus_one_even_eq_central {r : ℕ} (hr : 1 ≤ r) :
    binaryProbability (2 * r - 1) (fun p ↦ p.eval (-1) = 0) =
      ((r : ℝ) - 1) / ((r : ℝ) + 1) * centralBinomialMass r := by
  rw [binaryProbability_minus_one_even hr, centralBinomialMass_eq_choose]
  have hp : (2 : ℝ) ^ (2 * r) = 2 * (2 : ℝ) ^ (2 * r - 1) := by
    have he : 2 * r = (2 * r - 1) + 1 := by omega
    conv_lhs => rw [he, pow_succ]
    ring
  have h := adjacent_even_choose_identity hr
  rw [hp]
  have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  nlinarith

end OdlyzkoPoonen
