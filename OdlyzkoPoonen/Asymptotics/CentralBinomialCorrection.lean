import OdlyzkoPoonen.Asymptotics.CentralBinomial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# First correction to the central binomial probability

The exact recurrence and the Wallis bounds give sharper estimates by
telescoping. The normalized square lies between `1-1/(4*n)` and
`1-1/(4*(n+1))`; this determines its first correction with an explicit
second-order error.
-/

namespace OdlyzkoPoonen
open Filter
open scoped Topology

lemma centralBinomialMass_succ (n : ℕ) :
    centralBinomialMass (n + 1) =
      (2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1)) * centralBinomialMass n := by
  have hc : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  unfold centralBinomialMass
  rw [pow_succ]
  field_simp
  nlinarith [hc]

noncomputable def normalizedCentralBinomialSquare (n : ℕ) : ℝ :=
  Real.pi * (n : ℝ) * centralBinomialMass n ^ 2

lemma normalizedCentralBinomialSquare_step (n : ℕ) :
    normalizedCentralBinomialSquare (n + 1) - normalizedCentralBinomialSquare n =
      Real.pi * centralBinomialMass n ^ 2 / (4 * ((n : ℝ) + 1)) := by
  unfold normalizedCentralBinomialSquare
  rw [centralBinomialMass_succ]
  push_cast
  field_simp
  ring

lemma normalizedCentralBinomialSquare_le_one {n : ℕ} (hn : 1 ≤ n) :
    normalizedCentralBinomialSquare n ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := (le_div_iff₀ (mul_pos Real.pi_pos hn0)).mp
    (centralBinomialMass_sq_upper hn)
  unfold normalizedCentralBinomialSquare
  nlinarith

lemma normalizedCentralBinomialSquare_lower {n : ℕ} (hn : 1 ≤ n) :
    1 - 1 / (2 * (n : ℝ) + 1) ≤ normalizedCentralBinomialSquare n := by
  have h := mul_le_mul_of_nonneg_left (centralBinomialMass_sq_lower n)
    (show 0 ≤ Real.pi * (n : ℝ) by positivity)
  have he : Real.pi * (n : ℝ) * (2 / (Real.pi * (2 * (n : ℝ) + 1))) =
      1 - 1 / (2 * (n : ℝ) + 1) := by
    field_simp
    ring
  rw [he] at h
  exact h

lemma tendsto_normalizedCentralBinomialSquare :
    Tendsto (fun n : ℕ ↦ normalizedCentralBinomialSquare (n + 1)) atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ ↦ 2 * ((n : ℝ) + 1) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1
      ((tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2))
  have hlow : Tendsto (fun n : ℕ ↦ 1 - 1 / (2 * ((n : ℝ) + 1) + 1)) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hden)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
  · intro n
    simpa only [Nat.cast_add, Nat.cast_one] using
      normalizedCentralBinomialSquare_lower (n := n + 1) (by omega)
  · intro n
    exact normalizedCentralBinomialSquare_le_one (by omega)

lemma normalizedCentralBinomialSquare_step_upper {n : ℕ} (hn : 1 ≤ n) :
    normalizedCentralBinomialSquare (n + 1) - normalizedCentralBinomialSquare n ≤
      1 / (4 * (n : ℝ)) - 1 / (4 * ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := mul_le_mul_of_nonneg_left (centralBinomialMass_sq_upper hn)
    (show 0 ≤ Real.pi / (4 * ((n : ℝ) + 1)) by positivity)
  have he : Real.pi / (4 * ((n : ℝ) + 1)) * (1 / (Real.pi * (n : ℝ))) =
      1 / (4 * (n : ℝ)) - 1 / (4 * ((n : ℝ) + 1)) := by
    field_simp
    ring
  rw [he] at h
  rw [normalizedCentralBinomialSquare_step]
  simpa only [div_mul_eq_mul_div] using h

lemma normalizedCentralBinomialSquare_step_lower (n : ℕ) :
    1 / (4 * ((n : ℝ) + 1)) - 1 / (4 * ((n : ℝ) + 2)) ≤
      normalizedCentralBinomialSquare (n + 1) - normalizedCentralBinomialSquare n := by
  rw [normalizedCentralBinomialSquare_step]
  have h := mul_le_mul_of_nonneg_left (centralBinomialMass_sq_lower n)
    (show 0 ≤ Real.pi / (4 * ((n : ℝ) + 1)) by positivity)
  have hscale : 1 / (4 * ((n : ℝ) + 1)) - 1 / (4 * ((n : ℝ) + 2)) ≤
      Real.pi / (4 * ((n : ℝ) + 1)) *
        (2 / (Real.pi * (2 * (n : ℝ) + 1))) := by
    field_simp
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  simpa only [div_mul_eq_mul_div] using hscale.trans h

end OdlyzkoPoonen
