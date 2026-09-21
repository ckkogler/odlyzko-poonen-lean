import OdlyzkoPoonen.Asymptotics.PeriodicMonicIntegral
import OdlyzkoPoonen.Analysis.AffineHalfPowerExpansion
import OdlyzkoPoonen.Analysis.ResidueClassBounds

/-!
# Periodic half-power expansions for monic divisibility

Coefficients depend only on the residue of the internal-bit count modulo twice
a fixed zero-sum period. The powers and error term are indexed by the full
polynomial degree. All residue classes share a single asymptotic bound.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics
open scoped BigOperators Classical

theorem binaryProbability_monic_residue_expansion {f : ℤ[X]} (hf : f.Monic)
    (hd : 0 < f.natDegree) {q : ℕ} (hq : 0 < q) (hperiod : f ∣ X ^ q - 1)
    (hgeom : f ∣ ∑ j ∈ Finset.range q, (X : ℤ[X]) ^ j) (R : ℕ) (hR : 1 ≤ R) :
    ∃ c : Fin (2 * q) → ℕ → ℝ, (∀ r, c r 0 = 0) ∧
      (fun m : ℕ ↦ binaryProbability m (fun p ↦ f ∣ p) -
        ∑ j ∈ Finset.range (2 * R), c ⟨m % (2 * q), Nat.mod_lt _ (by omega)⟩ j *
          ((m : ℝ) + 1) ^ (-(j : ℝ) / 2)) =O[atTop]
            (fun m : ℕ ↦ ((m : ℝ) + 1) ^ (-(R : ℝ))) := by
  have h2q : 0 < 2 * q := by omega
  have hex (r : Fin (2 * q)) : ∃ c : ℕ → ℝ, c 0 = 0 ∧
      (fun k : ℕ ↦ binaryProbability (2 * q * k + r.val) (fun p ↦ f ∣ p) -
        ∑ j ∈ Finset.range (2 * R), c j *
          ((2 * q * k + (r.val + 1) : ℕ) : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop]
            (fun k : ℕ ↦ ((2 * q * k + (r.val + 1) : ℕ) : ℝ) ^ (-(R : ℝ))) := by
    obtain ⟨c, hc0, hc⟩ := binaryProbability_periodic_monic_block_expansion
      hf hd hq hperiod hgeom r.val R hR
    exact half_power_expansion_affine h2q (r.val + 1) R hc0 hc
  choose c hc0 hc using hex
  refine ⟨c, hc0, isBigO_of_residue_classes h2q ?_⟩
  intro r
  have hmod (k : ℕ) : (2 * q * k + r.val) % (2 * q) = r.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt r.isLt]
  simpa only [hmod, Fin.eta, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat, add_assoc] using hc r

/-- Degree indexing, with residue dependence written as `(n-1) mod (2*q)`. -/
theorem degreeProbability_monic_residue_expansion {f : ℤ[X]} (hf : f.Monic)
    (hd : 0 < f.natDegree) {q : ℕ} (hq : 0 < q) (hperiod : f ∣ X ^ q - 1)
    (hgeom : f ∣ ∑ j ∈ Finset.range q, (X : ℤ[X]) ^ j) (R : ℕ) (hR : 1 ≤ R) :
    ∃ c : Fin (2 * q) → ℕ → ℝ, (∀ r, c r 0 = 0) ∧
      (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ f ∣ p) -
        ∑ j ∈ Finset.range (2 * R), c ⟨(n - 1) % (2 * q), Nat.mod_lt _ (by omega)⟩ j *
          (n : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop]
            (fun n : ℕ ↦ (n : ℝ) ^ (-(R : ℝ))) := by
  obtain ⟨c, hc0, hc⟩ := binaryProbability_monic_residue_expansion hf hd hq hperiod hgeom R hR
  refine ⟨c, hc0, ?_⟩
  have ht : Tendsto (fun n : ℕ ↦ n - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b + 1)] with n hn
    omega
  have he := hc.comp_tendsto ht
  apply he.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      exact_mod_cast Nat.sub_add_cancel hn
    dsimp only [Function.comp_def]
    rw [hn']
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      exact_mod_cast Nat.sub_add_cancel hn
    dsimp only [Function.comp_def]
    rw [hn']

end OdlyzkoPoonen
