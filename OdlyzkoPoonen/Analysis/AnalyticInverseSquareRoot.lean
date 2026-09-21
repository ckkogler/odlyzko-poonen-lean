import OdlyzkoPoonen.Analysis.HalfPowerTruncation
import OdlyzkoPoonen.Analysis.GaussianScaling
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Scalar analytic expansions at inverse square roots

Taylor expansion at zero becomes a fixed half-power expansion at infinity.
An analytic change of variable accounts for an affine change in the index.
-/

namespace OdlyzkoPoonen
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators ContDiff

lemma scalar_multilinear_diagonal (p : FormalMultilinearSeries ℝ ℝ ℝ) (j : ℕ) (x : ℝ) :
    p j (fun _ ↦ x) = p j (fun _ ↦ 1) * x ^ j := by
  simpa only [smul_eq_mul, mul_one, mul_comm, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (p j).map_smul_univ (fun _ ↦ x) (fun _ ↦ (1 : ℝ))

/-- Every scalar analytic function has a half-power expansion after this substitution. -/
theorem analytic_inverse_sqrt_expansion {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (N : ℕ) :
    ∃ c : ℕ → ℝ, c 0 = f 0 ∧
      (fun n : ℕ ↦ f ((Real.sqrt (n : ℝ))⁻¹) -
        ∑ j ∈ Finset.range N, c j * (n : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop]
          (fun n : ℕ ↦ (n : ℝ) ^ (-(N : ℝ) / 2)) := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨fun j ↦ p j (fun _ ↦ 1), ?_, ?_⟩
  · exact hp.coeff_zero _
  · have hpartial (x : ℝ) : p.partialSum N x =
        ∑ j ∈ Finset.range N, p j (fun _ ↦ 1) * x ^ j := by
      unfold FormalMultilinearSeries.partialSum
      apply Finset.sum_congr rfl
      intro j _
      exact scalar_multilinear_diagonal p j x
    have he := (hp.isBigO_sub_partialSum_pow N).comp_tendsto tendsto_inverse_sqrt_nat
    simp only [Function.comp_def, zero_add, hpartial, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, inverse_sqrt_pow_eq_rpow (Nat.cast_nonneg _)] at he
    exact he

/-- The inverse square root coordinate for an affine index `q*k+s`. -/
def affineInverseSqrt (q s x : ℝ) : ℝ :=
  Real.sqrt q * x / Real.sqrt (1 - s * x ^ 2)

lemma affineInverseSqrt_zero (q s : ℝ) : affineInverseSqrt q s 0 = 0 := by
  simp [affineInverseSqrt]

lemma affineInverseSqrt_analyticAt (q s : ℝ) : AnalyticAt ℝ (affineInverseSqrt q s) 0 := by
  have h : ContDiffAt ℝ ω (affineInverseSqrt q s) 0 := by
    unfold affineInverseSqrt
    apply ContDiffAt.div
    · fun_prop
    · apply (Real.contDiffAt_sqrt (by norm_num : (1 - s * (0 : ℝ) ^ 2) ≠ 0)).comp 0
        (show ContDiffAt ℝ ω (fun x : ℝ ↦ 1 - s * x ^ 2) 0 by fun_prop)
    · norm_num
  exact h.analyticAt

lemma affineInverseSqrt_at_index {q k s : ℝ} (hq : 0 < q) (hk : 0 < k) (hs : 0 ≤ s) :
    affineInverseSqrt q s ((Real.sqrt (q * k + s))⁻¹) = (Real.sqrt k)⁻¹ := by
  have hn : 0 < q * k + s := by positivity
  have hsqrt : 0 < Real.sqrt (q * k + s) := Real.sqrt_pos.2 hn
  have hinside : 1 - s * ((Real.sqrt (q * k + s))⁻¹) ^ 2 =
      q * k / (q * k + s) := by
    rw [inv_pow, Real.sq_sqrt hn.le]
    field_simp
    ring
  rw [affineInverseSqrt, hinside, Real.sqrt_div (mul_nonneg hq.le hk.le),
    Real.sqrt_mul hq.le]
  have hqroot := Real.sqrt_pos.2 hq
  have hkroot := Real.sqrt_pos.2 hk
  field_simp

end
end OdlyzkoPoonen
