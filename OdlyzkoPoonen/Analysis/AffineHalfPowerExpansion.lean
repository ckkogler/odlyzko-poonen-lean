import OdlyzkoPoonen.Analysis.AnalyticInverseSquareRoot
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Half-power expansions under affine changes of index

A fixed polynomial in the inverse square root of a block count becomes an
analytic function of the inverse square root of the original index. Taylor
truncation preserves the requested error order and yields fixed coefficients.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped Topology BigOperators

lemma nat_affine_tendsto {q : ℕ} (hq : 0 < q) (s : ℕ) :
    Tendsto (fun k : ℕ ↦ q * k + s) atTop atTop := by
  apply tendsto_atTop_mono (fun k ↦ ?_) tendsto_id
  change k ≤ q * k + s
  nlinarith

lemma nat_affine_rpow_isTheta {q : ℕ} (hq : 0 < q) (s : ℕ) (a : ℝ) :
    (fun k : ℕ ↦ ((q * k + s : ℕ) : ℝ) ^ a) =Θ[atTop]
      (fun k : ℕ ↦ (k : ℝ) ^ a) := by
  have hlin : (fun k : ℕ ↦ ((q * k + s : ℕ) : ℝ)) =Θ[atTop]
      (fun k : ℕ ↦ (k : ℝ)) := by
    constructor
    · apply isBigO_iff.mpr
      refine ⟨(q : ℝ) + s, ?_⟩
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      simp only [Real.norm_eq_abs, Nat.abs_cast, Nat.cast_add, Nat.cast_mul]
      rw [abs_of_nonneg (by positivity)]
      nlinarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
    · apply isBigO_iff.mpr
      refine ⟨1, ?_⟩
      filter_upwards [] with k
      have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
      simp only [Real.norm_eq_abs, Nat.abs_cast, Nat.cast_add, Nat.cast_mul, one_mul]
      rw [abs_of_nonneg (by positivity)]
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  exact hlin.rpow (Eventually.of_forall (fun _ ↦ Nat.cast_nonneg _))
    (Eventually.of_forall (fun _ ↦ Nat.cast_nonneg _))

/-- Convert a block-count expansion to an expansion in the full affine index. -/
theorem half_power_expansion_affine {F : ℕ → ℝ} {q : ℕ} (hq : 0 < q) (s R : ℕ)
    {c : ℕ → ℝ} (hc : c 0 = 0)
    (hF : (fun k : ℕ ↦ F k - ∑ j ∈ Finset.range (2 * R),
      c j * (k : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop] (fun k : ℕ ↦ (k : ℝ) ^ (-(R : ℝ)))) :
    ∃ b : ℕ → ℝ, b 0 = 0 ∧
      (fun k : ℕ ↦ F k - ∑ j ∈ Finset.range (2 * R),
        b j * ((q * k + s : ℕ) : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop]
          (fun k : ℕ ↦ ((q * k + s : ℕ) : ℝ) ^ (-(R : ℝ))) := by
  let g : ℝ → ℝ := fun x ↦ ∑ j ∈ Finset.range (2 * R),
    c j * affineInverseSqrt q s x ^ j
  have hga : AnalyticAt ℝ g 0 := by
    apply Finset.analyticAt_fun_sum
    intro j _
    exact analyticAt_const.mul ((affineInverseSqrt_analyticAt q s).pow j)
  have hg0 : g 0 = 0 := by
    simp only [g, affineInverseSqrt_zero]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j = 0
    · simp [hj, hc]
    · simp [hj]
  obtain ⟨b, hb0, hb⟩ := analytic_inverse_sqrt_expansion hga (2 * R)
  refine ⟨b, hb0.trans hg0, ?_⟩
  have hb' := hb.comp_tendsto (nat_affine_tendsto hq s)
  have hexp : -((2 * R : ℕ) : ℝ) / 2 = -(R : ℝ) := by push_cast; ring
  simp only [Function.comp_def, hexp] at hb'
  have hsum : (fun k : ℕ ↦ g ((Real.sqrt ((q * k + s : ℕ) : ℝ))⁻¹)) =ᶠ[atTop]
      (fun k : ℕ ↦ ∑ j ∈ Finset.range (2 * R), c j * (k : ℝ) ^ (-(j : ℝ) / 2)) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    dsimp only [g]
    rw [Nat.cast_add, Nat.cast_mul, affineInverseSqrt_at_index hq' hk' (Nat.cast_nonneg s)]
    simp only [inv_pow, inverse_sqrt_pow_eq_rpow (Nat.cast_nonneg k)]
  have hFb := hF.trans (nat_affine_rpow_isTheta hq s (-(R : ℝ))).symm.isBigO
  have hh : (fun k : ℕ ↦ F k - g ((Real.sqrt ((q * k + s : ℕ) : ℝ))⁻¹))
      =O[atTop] (fun k : ℕ ↦ ((q * k + s : ℕ) : ℝ) ^ (-(R : ℝ))) :=
    hFb.congr' (hsum.mono (fun k hk ↦ by dsimp only at hk ⊢; rw [hk])) (Eventually.of_forall (fun _ ↦ rfl))
  simpa only [sub_add_sub_cancel] using hh.add hb'

end OdlyzkoPoonen
