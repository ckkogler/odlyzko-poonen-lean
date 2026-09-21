import OdlyzkoPoonen.Asymptotics.MonicGaussianLeadingTerm
import OdlyzkoPoonen.Analysis.AffinePowerLeadingTerm
import OdlyzkoPoonen.Analysis.ResidueClassBounds

/-!
# Degree-indexed leading constants for periodic monic divisors

The Gaussian coefficient is independent of the residual block. The affine
power estimate and finite residue gluing give one degree-indexed asymptotic.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics
open scoped BigOperators Classical

theorem binaryProbability_monic_gaussian_leading_term {f : ℤ[X]} (hf : f.Monic)
    {q : ℕ} (hq : 0 < q) (hperiod : f ∣ X ^ q - 1)
    (hgeom : f ∣ ∑ j ∈ Finset.range q, (X : ℤ[X]) ^ j) :
    (fun m : ℕ ↦ binaryProbability m (fun p ↦ f ∣ p) -
      ((m : ℝ) + 1) ^ (-(f.natDegree : ℝ) / 2) *
        ((2 * q : ℕ) : ℝ) ^ ((f.natDegree : ℝ) / 2) * monicDivisorGaussianVolume f q)
      =O[atTop] (fun m : ℕ ↦ ((m : ℝ) + 1) ^ (-(f.natDegree : ℝ) / 2 - 1)) := by
  have h2q : 0 < 2 * q := by omega
  apply isBigO_of_residue_classes h2q
  intro r
  have hblock := binaryProbability_periodic_monic_block_leading_term hf hq hperiod hgeom r.val
  have hblock' := hblock.trans
    (nat_affine_rpow_isTheta h2q (r.val + 1) (-(f.natDegree : ℝ) / 2 - 1)).symm.isBigO
  have hchange := (affine_rpow_leading_error h2q (r.val + 1) (-(f.natDegree : ℝ) / 2)).const_mul_left
    (monicDivisorGaussianVolume f q)
  have he := hblock'.add hchange
  have hneg : -(-(f.natDegree : ℝ) / 2) = (f.natDegree : ℝ) / 2 := by ring
  simp only [hneg] at he
  convert! he using 1
  · funext k
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_assoc]
    ring
  · funext k
    congr 1
    push_cast
    ring

/-- The leading constant in the full polynomial degree, with one-power better remainder. -/
theorem degreeProbability_monic_gaussian_leading_term {f : ℤ[X]} (hf : f.Monic)
    {q : ℕ} (hq : 0 < q) (hperiod : f ∣ X ^ q - 1)
    (hgeom : f ∣ ∑ j ∈ Finset.range q, (X : ℤ[X]) ^ j) :
    (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ f ∣ p) -
      (n : ℝ) ^ (-(f.natDegree : ℝ) / 2) *
        ((2 * q : ℕ) : ℝ) ^ ((f.natDegree : ℝ) / 2) * monicDivisorGaussianVolume f q)
      =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-(f.natDegree : ℝ) / 2 - 1)) := by
  have ht : Tendsto (fun n : ℕ ↦ n - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b + 1)] with n hn
    omega
  have he := (binaryProbability_monic_gaussian_leading_term hf hq hperiod hgeom).comp_tendsto ht
  apply he.congr'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast Nat.sub_add_cancel hn
    dsimp only [Function.comp_def]
    rw [hn']
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast Nat.sub_add_cancel hn
    dsimp only [Function.comp_def]
    rw [hn']

end OdlyzkoPoonen
