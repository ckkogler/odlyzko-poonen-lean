import OdlyzkoPoonen.Analysis.CosineExpansion
import OdlyzkoPoonen.Analysis.AnalyticRemainder
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Quartic Gaussian approximation for cosine products

Telescoping products of factors bounded by one reduces the multivariate
estimate to the scalar fourth-order cosine and exponential remainders.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped BigOperators Topology

lemma abs_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    rw [Finset.prod_insert his, Finset.prod_insert his, Finset.sum_insert his]
    have hs := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hg j (Finset.mem_insert_of_mem hj))
    have hpg : |∏ j ∈ s, g j| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) (fun j hj ↦ hg j (Finset.mem_insert_of_mem hj))
    calc
      _ = |f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j) +
          (f i - g i) * ∏ j ∈ s, g j| := by congr 1; ring
      _ ≤ |f i| * |(∏ j ∈ s, f j) - ∏ j ∈ s, g j| +
          |f i - g i| * |∏ j ∈ s, g j| := by
        simpa only [abs_mul] using abs_add_le
          (f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j))
          ((f i - g i) * ∏ j ∈ s, g j)
      _ ≤ 1 * (∑ j ∈ s, |f j - g j|) + |f i - g i| * 1 := by
        gcongr
        exact hf i (Finset.mem_insert_self _ _)
      _ = _ := by ring

lemma cosine_sq_quadratic_remainder (x : ℝ) :
    |Real.cos x ^ 2 - (1 - x ^ 2)| ≤ x ^ 4 / 3 := by
  have hc := cosine_quadratic_remainder_bound (2 * x)
  rw [Real.cos_two_mul] at hc
  rw [abs_le] at hc ⊢
  constructor <;> nlinarith

lemma cosine_sq_gaussian_quartic {x : ℝ} (hx : |x| ≤ 1) :
    |Real.cos x ^ 2 - Real.exp (-(x ^ 2))| ≤ 2 * x ^ 4 := by
  have hx2 : |-(x ^ 2)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs x, abs_nonneg x]
  have he := Real.abs_exp_sub_one_sub_id_le hx2
  have he' : |(1 - x ^ 2) - Real.exp (-(x ^ 2))| ≤ x ^ 4 := by
    rw [abs_sub_comm]
    convert he using 1
    · congr 1; ring
    · ring
  calc
    _ ≤ |Real.cos x ^ 2 - (1 - x ^ 2)| + |(1 - x ^ 2) - Real.exp (-(x ^ 2))| :=
      abs_sub_le _ _ _
    _ ≤ x ^ 4 / 3 + x ^ 4 := add_le_add (cosine_sq_quadratic_remainder x) he'
    _ ≤ _ := by nlinarith [sq_nonneg (x ^ 2)]

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- The nonnegative characteristic factor associated to a doubled period. -/
noncomputable def cosineSquareProduct (L : ι → V →L[ℝ] ℝ) (x : V) : ℝ :=
  ∏ i, Real.cos (L i x) ^ 2

/-- The quadratic form determined by the linear coordinate vectors. -/
noncomputable def cosineQuadraticForm (L : ι → V →L[ℝ] ℝ) (x : V) : ℝ :=
  ∑ i, (L i x) ^ 2

theorem cosineSquareProduct_gaussian_isBigO (L : ι → V →L[ℝ] ℝ) :
    (fun x ↦ cosineSquareProduct L x - Real.exp (-cosineQuadraticForm L x))
      =O[𝓝 0] (fun x : V ↦ ‖x‖ ^ 4) := by
  have he : ∀ᶠ x : V in 𝓝 0, ∀ i, |L i x| ≤ 1 := by
    apply eventually_all.mpr
    intro i
    have ht : Tendsto (fun x : V ↦ |L i x|) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero, abs_zero] using (L i).continuous.abs.tendsto (0 : V)
    filter_upwards [(tendsto_order.mp ht).2 1 (by norm_num)] with x hx
    exact hx.le
  refine isBigO_iff.mpr ⟨2 * ∑ i, ‖L i‖ ^ 4, ?_⟩
  filter_upwards [he] with x hx
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  have hprod : (∏ i, Real.exp (-(L i x) ^ 2)) = Real.exp (-cosineQuadraticForm L x) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
    rfl
  rw [cosineSquareProduct, ← hprod]
  calc
    _ ≤ ∑ i, |Real.cos (L i x) ^ 2 - Real.exp (-(L i x) ^ 2)| := by
      apply abs_prod_sub_prod_le_sum
      · intro i _
        rw [abs_of_nonneg (sq_nonneg _)]
        exact Real.cos_sq_le_one _
      · intro i _
        rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        exact neg_nonpos.mpr (sq_nonneg _)
    _ ≤ ∑ i, 2 * (‖L i‖ * ‖x‖) ^ 4 := by
      apply Finset.sum_le_sum
      intro i _
      apply (cosine_sq_gaussian_quartic (hx i)).trans
      have hpow : |L i x| ^ 4 = (L i x) ^ 4 := by
        rw [pow_abs, abs_of_nonneg (by positivity)]
      rw [← hpow]
      gcongr
      exact (L i).le_opNorm x
    _ = _ := by simp_rw [mul_pow]; rw [← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]

end OdlyzkoPoonen
