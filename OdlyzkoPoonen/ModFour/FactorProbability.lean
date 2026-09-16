import OdlyzkoPoonen.ModFour.ShiftedSlopes
import OdlyzkoPoonen.Probability.AsymmetryLaw
import OdlyzkoPoonen.Probability.FiniteBounds
import OdlyzkoPoonen.Probability.AsymmetryGeometricSum

/-!
# The factor-pair probability bound

Choose independent uniform endpoint-one polynomials over the field with two
elements. Partition a nonreciprocal first factor by its first asymmetric pair.
The exact probability of that pair, combined with the proved fixed-factor
congruence estimate, sums to at most twice `(3/4)` to the number of exposed
opposite pairs of the second factor. No factor coprimality is required.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

/-- Contribution of a prescribed first asymmetric pair. -/
lemma f2PairProbability_first_asymmetry_contribution {s n : ℕ}
    (i : Fin (s / 2)) (hi : i.val + 1 ≤ n / 2) :
    f2PairProbability s n (fun a b ↦ FirstAsymmetryAt a (i.val + 1) ∧
      CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
        (autocorrelation (zeroOneLift (a * b.reverse)))) ≤
      (1 / 2 : ℝ) ^ (i.val + 1) * (3 / 4 : ℝ) ^ (n / 2 - (i.val + 1)) := by
  let F (u : Fin s → Bool) : Prop := FirstAsymmetryAt (f2WordPolynomial u) (i.val + 1)
  let C (u : Fin s → Bool) (v : Fin n → Bool) : Prop :=
    CongruentMod 4 (autocorrelation (zeroOneLift (f2WordPolynomial u * f2WordPolynomial v)))
      (autocorrelation (zeroOneLift (f2WordPolynomial u * (f2WordPolynomial v).reverse)))
  have hfiber (u : Fin s → Bool) (hu : F u) :
      uniformProbability (C u) ≤ (3 / 4 : ℝ) ^ (n / 2 - (i.val + 1)) := by
    change f2Probability n (fun b ↦
      CongruentMod 4 (autocorrelation (zeroOneLift (f2WordPolynomial u * b)))
        (autocorrelation (zeroOneLift (f2WordPolynomial u * b.reverse)))) ≤ _
    exact f2_factor_congruence_probability_le_of_firstAsymmetry
      (f2WordPolynomial_endpoints u) hu hi
  have hprob : uniformProbability F = (1 / 2 : ℝ) ^ (i.val + 1) := by
    change f2Probability s (fun a ↦ FirstAsymmetryAt a (i.val + 1)) = _
    exact f2Probability_firstAsymmetryAt i
  have h := uniformProbability_product_bound F C
    ((3 / 4 : ℝ) ^ (n / 2 - (i.val + 1))) hfiber
  rw [hprob] at h
  exact h

/-- The factor-pair bound in the internal-word degree convention. -/
lemma f2PairProbability_factor_congruence_le {s n : ℕ} (hs : s ≤ n) :
    f2PairProbability s n (fun a b ↦ a ≠ a.reverse ∧
      CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
        (autocorrelation (zeroOneLift (a * b.reverse)))) ≤
      2 * (3 / 4 : ℝ) ^ (n / 2) := by
  classical
  unfold f2PairProbability
  let C (u : Fin s → Bool) (v : Fin n → Bool) : Prop :=
    CongruentMod 4 (autocorrelation (zeroOneLift (f2WordPolynomial u * f2WordPolynomial v)))
      (autocorrelation (zeroOneLift (f2WordPolynomial u * (f2WordPolynomial v).reverse)))
  let F (i : Fin (s / 2)) (u : Fin s → Bool) : Prop :=
    FirstAsymmetryAt (f2WordPolynomial u) (i.val + 1)
  have hhalf : s / 2 ≤ n / 2 := Nat.div_le_div_right hs
  change uniformProbability (fun v : (Fin s → Bool) × (Fin n → Bool) ↦
    f2WordPolynomial v.1 ≠ (f2WordPolynomial v.1).reverse ∧ C v.1 v.2) ≤ _
  calc
    _ ≤ uniformProbability (fun v : (Fin s → Bool) × (Fin n → Bool) ↦
        ∃ i : Fin (s / 2), F i v.1 ∧ C v.1 v.2) := by
      apply uniformProbability_mono
      intro v hv
      obtain ⟨i, hi⟩ := (f2WordPolynomial_endpoints v.1).exists_firstAsymmetry hv.1
      exact ⟨i, hi, hv.2⟩
    _ ≤ ∑ i : Fin (s / 2), uniformProbability
        (fun v : (Fin s → Bool) × (Fin n → Bool) ↦ F i v.1 ∧ C v.1 v.2) :=
      uniformProbability_exists_le_sum
        (fun (i : Fin (s / 2)) (v : (Fin s → Bool) × (Fin n → Bool)) ↦ F i v.1 ∧ C v.1 v.2)
    _ ≤ ∑ i : Fin (s / 2), (1 / 2 : ℝ) ^ (i.val + 1) *
        (3 / 4 : ℝ) ^ (n / 2 - (i.val + 1)) := by
      apply Finset.sum_le_sum
      intro i _
      have hi : i.val + 1 ≤ n / 2 := by have := i.isLt; omega
      simpa only [f2PairProbability, F, C] using
        f2PairProbability_first_asymmetry_contribution (n := n) i hi
    _ ≤ _ := asymmetry_geometric_sum_le hhalf

/-- For independent uniform monic endpoint-one factors of degrees `1 ≤ d ≤ e`,
the chance of a nonreciprocal first factor and modulo-four agreement of the
lifted autocorrelations is at most `2*(3/4)^floor((e-1)/2)`. -/
theorem factor_pair_congruence_probability (d e : ℕ) (hd : 1 ≤ d) (hde : d ≤ e) :
    f2PairProbability (d - 1) (e - 1) (fun a b ↦ a ≠ a.reverse ∧
      CongruentMod 4 (autocorrelation (zeroOneLift (a * b)))
        (autocorrelation (zeroOneLift (a * b.reverse)))) ≤
      2 * (3 / 4 : ℝ) ^ ((e - 1) / 2) := by
  exact f2PairProbability_factor_congruence_le (by omega)

end OdlyzkoPoonen
