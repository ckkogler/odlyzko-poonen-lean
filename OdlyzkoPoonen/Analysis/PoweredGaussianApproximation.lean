import OdlyzkoPoonen.Analysis.GaussianIntegralBounds
import OdlyzkoPoonen.Analysis.PoweredPerturbation

/-!
# Gaussian approximation of large powers

A quartic perturbation of a Gaussian admits a finite binomial expansion
whose integrated remainder gains one inverse power per retained term.
-/

namespace OdlyzkoPoonen
open MeasureTheory Filter Asymptotics
open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma powered_gaussian_remainder_bound {ψ Q h : V → ℝ} {b C H : ℝ}
    (hb : 0 < b) (_hC : 0 ≤ C) (hH : 0 ≤ H) (n R : ℕ)
    (hR : 1 ≤ R) (hn : 2 * R ≤ n) (x : V)
    (hψ0 : 0 ≤ ψ x) (hψ : ψ x ≤ Real.exp (-b * ‖x‖ ^ 2))
    (hQ : b * ‖x‖ ^ 2 ≤ Q x)
    (hδ : |ψ x - Real.exp (-Q x)| ≤ C * ‖x‖ ^ 4) (hh : |h x| ≤ H) :
    |h x * (ψ x ^ n - truncatedPowerExpansion n R (ψ x) (Real.exp (-Q x)))| ≤
      (H * C ^ R * (n : ℝ) ^ R) *
        (‖x‖ ^ (4 * R) * Real.exp (-((n : ℝ) * (b / 2)) * ‖x‖ ^ 2)) := by
  have hg : Real.exp (-Q x) ≤ Real.exp (-b * ‖x‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  have he := pow_sub_truncatedPowerExpansion_le n R hR hψ0 (Real.exp_pos _).le hψ hg
  have hchoose : (n.choose R : ℝ) ≤ (n : ℝ) ^ R := by exact_mod_cast Nat.choose_le_pow n R
  have hnp : (n : ℝ) / 2 ≤ (n - R : ℕ) := by
    have hrn : R ≤ n := by omega
    rw [Nat.cast_sub hrn]
    have hn' : 2 * (R : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hexp : Real.exp (-b * ‖x‖ ^ 2) ^ (n - R) ≤
      Real.exp (-((n : ℝ) * (b / 2)) * ‖x‖ ^ 2) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_right hnp (mul_nonneg hb.le (sq_nonneg ‖x‖))
    nlinarith
  rw [abs_mul]
  calc
    _ ≤ H * ((n.choose R : ℝ) * Real.exp (-b * ‖x‖ ^ 2) ^ (n - R) *
        |ψ x - Real.exp (-Q x)| ^ R) :=
      mul_le_mul hh he (abs_nonneg _) hH
    _ ≤ H * ((n : ℝ) ^ R *
        Real.exp (-((n : ℝ) * (b / 2)) * ‖x‖ ^ 2) * (C * ‖x‖ ^ 4) ^ R) := by
      gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- Integrated power expansions have the full expected polynomial remainder. -/
theorem powered_gaussian_remainder_isBigO {K : Set V} (hK : MeasurableSet K)
    {ψ Q h : V → ℝ} {b C H : ℝ} (hb : 0 < b) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (R : ℕ) (hR : 1 ≤ R)
    (hψ0 : ∀ x ∈ K, 0 ≤ ψ x)
    (hψ : ∀ x ∈ K, ψ x ≤ Real.exp (-b * ‖x‖ ^ 2))
    (hQ : ∀ x ∈ K, b * ‖x‖ ^ 2 ≤ Q x)
    (hδ : ∀ x ∈ K, |ψ x - Real.exp (-Q x)| ≤ C * ‖x‖ ^ 4)
    (hh : ∀ x ∈ K, |h x| ≤ H) :
    (fun n : ℕ ↦ ∫ x in K,
      h x * (ψ x ^ n - truncatedPowerExpansion n R (ψ x) (Real.exp (-Q x))))
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-(Module.finrank ℝ V : ℝ) / 2 - R)) := by
  let J := ∫ x : V, ‖x‖ ^ (4 * R) * Real.exp (-(b / 2) * ‖x‖ ^ 2)
  refine isBigO_iff.mpr ⟨H * C ^ R * J, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * R)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  simp only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
  have he := abs_setIntegral_le_gaussian_moment hK (4 * R)
    (C := H * C ^ R * (n : ℝ) ^ R) (by positivity) (b := b / 2) (by linarith) hn0
    (fun x hx ↦ powered_gaussian_remainder_bound hb hC hH n R hR hn x
      (hψ0 x hx) (hψ x hx) (hQ x hx) (hδ x hx) (hh x hx))
  have hp : (n : ℝ) ^ R * (n : ℝ) ^ (-((Module.finrank ℝ V : ℝ) + (4 * R : ℕ)) / 2) =
      (n : ℝ) ^ (-(Module.finrank ℝ V : ℝ) / 2 - R) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn0]
    congr 1
    push_cast
    ring
  calc
    _ ≤ (H * C ^ R * (n : ℝ) ^ R) *
        (n : ℝ) ^ (-((Module.finrank ℝ V : ℝ) + (4 * R : ℕ)) / 2) * J := he
    _ = _ := by rw [mul_assoc (H * C ^ R), hp]; ring

end OdlyzkoPoonen
