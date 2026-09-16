import OdlyzkoPoonen.Arithmetic.BinaryLogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# A logarithmic cutoff with an exact exponential tail

Eight times one plus the integer binary logarithm is a positive degree cutoff.
The exact inequality `n^8 ≤ 2^cutoff` controls the high-degree tail. Its real
size is `O(log n)`, so every fixed power of the cutoff is negligible compared
with `sqrt(n)`. The floor inherent in the integer logarithm is fully accounted
for by the two proved integer logarithm inequalities.
-/

namespace OdlyzkoPoonen
open Filter
open scoped Topology

/-- A positive integer degree cutoff of logarithmic size. -/
def cyclotomicDegreeCutoff (n : ℕ) : ℕ := 8 * (Nat.log 2 n + 1)

lemma cyclotomicDegreeCutoff_pos (n : ℕ) : 0 < cyclotomicDegreeCutoff n := by
  unfold cyclotomicDegreeCutoff
  omega

lemma pow_eight_le_two_pow_cyclotomicDegreeCutoff (n : ℕ) :
    (n : ℝ) ^ 8 ≤ (2 : ℝ) ^ cyclotomicDegreeCutoff n := by
  exact_mod_cast nat_pow_le_two_pow_log_multiple n 8

lemma cyclotomicDegreeCutoff_le_log {n : ℕ} (hn : 1 ≤ n) :
    (cyclotomicDegreeCutoff n : ℝ) ≤ (8 / Real.log 2) * Real.log (n : ℝ) + 8 := by
  have h := natLog_two_le_real_log_div hn
  simp only [cyclotomicDegreeCutoff, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  calc
    _ ≤ 8 * (Real.log (n : ℝ) / Real.log 2 + 1) := by gcongr
    _ = _ := by ring

lemma cyclotomicDegreeCutoff_isBigO_log :
    (fun n : ℕ ↦ (cyclotomicDegreeCutoff n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  have ht : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine Asymptotics.isBigO_iff.mpr ⟨8 / Real.log 2 + 8, ?_⟩
  filter_upwards [eventually_ge_atTop 1, ht.eventually_ge_atTop 1] with n hn hlog
  have hL0 : (0 : ℝ) ≤ (cyclotomicDegreeCutoff n : ℝ) := Nat.cast_nonneg _
  simp only [Real.norm_eq_abs, abs_of_nonneg hL0,
    abs_of_nonneg (show 0 ≤ Real.log (n : ℝ) by linarith)]
  calc
    _ ≤ (8 / Real.log 2) * Real.log (n : ℝ) + 8 := cyclotomicDegreeCutoff_le_log hn
    _ ≤ _ := by nlinarith

lemma log_nat_pow_isLittleO_sqrt (d : ℕ) :
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ d) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
  have h := (isLittleO_log_rpow_rpow_atTop (d : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  simpa only [Function.comp_def, Real.rpow_natCast, ← Real.sqrt_eq_rpow] using h

lemma cyclotomicDegreeCutoff_pow_isLittleO_sqrt (d : ℕ) :
    (fun n : ℕ ↦ (cyclotomicDegreeCutoff n : ℝ) ^ d) =o[atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) :=
  (cyclotomicDegreeCutoff_isBigO_log.pow d).trans_isLittleO (log_nat_pow_isLittleO_sqrt d)

lemma tendsto_cyclotomicDegreeCutoff_pow_div_sqrt (d : ℕ) :
    Tendsto (fun n : ℕ ↦ (cyclotomicDegreeCutoff n : ℝ) ^ d / Real.sqrt (n : ℝ))
      atTop (𝓝 0) :=
  (cyclotomicDegreeCutoff_pow_isLittleO_sqrt d).tendsto_div_nhds_zero

lemma eventually_cyclotomic_cutoff_scale_le_one :
    ∀ᶠ n : ℕ in atTop, 8 * (cyclotomicDegreeCutoff n : ℝ) / Real.sqrt (n : ℝ) ≤ 1 := by
  have ht : Tendsto
      (fun n : ℕ ↦ 8 * (cyclotomicDegreeCutoff n : ℝ) / Real.sqrt (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero, mul_div_assoc] using
      (tendsto_cyclotomicDegreeCutoff_pow_div_sqrt 1).const_mul 8
  exact ht.eventually_le_const (by norm_num : (0 : ℝ) < 1)

end OdlyzkoPoonen
