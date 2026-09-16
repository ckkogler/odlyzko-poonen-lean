import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Elementary comparisons for the residue atom bound

Squaring the inverse-square-root scale removes the root without changing its
sign. For orders at most twice a squared degree cutoff, a common upper scale
is `8*L/sqrt(n)`. Its cube gives the fifth power of the cutoff after summing
over the possible orders.
-/

namespace OdlyzkoPoonen

lemma residue_atom_scale_sq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (4 / Real.sqrt (x / y)) ^ 2 = 16 * y / x := by
  rw [div_pow, Real.sq_sqrt (div_nonneg hx.le hy.le)]
  field_simp
  norm_num

lemma residue_atom_scale_le_cutoff {x y L : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hL : 0 ≤ L) (hyL : y ≤ 2 * L ^ 2) :
    4 / Real.sqrt (x / y) ≤ 8 * L / Real.sqrt x := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [residue_atom_scale_sq hx hy, div_pow, mul_pow, Real.sq_sqrt hx.le]
  apply div_le_div_of_nonneg_right _ hx.le
  nlinarith

lemma residue_order_count_mul_cube {x L : ℝ} (hx : 0 < x) :
    (2 * L ^ 2) * (8 * L / Real.sqrt x) ^ 3 =
      1024 * L ^ 5 / (x * Real.sqrt x) := by
  have hs : (Real.sqrt x) ^ 3 = x * Real.sqrt x := by
    rw [pow_succ, Real.sq_sqrt hx.le]
  rw [div_pow, hs]
  ring

end OdlyzkoPoonen
