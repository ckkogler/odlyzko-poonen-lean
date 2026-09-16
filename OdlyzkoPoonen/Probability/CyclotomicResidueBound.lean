import OdlyzkoPoonen.Probability.ResidueBlocks
import OdlyzkoPoonen.Probability.SelectedCoordinates
import OdlyzkoPoonen.Probability.BinaryModel

/-!
# A uniform fixed-order cyclotomic probability bound

Condition on all residue blocks with index at least the cyclotomic degree.
Divisibility determines the remaining coefficient sums, each of which has a
uniform atom bound. The product exponent is exactly the cyclotomic degree.
This argument includes fixed endpoint coefficients and empty residue blocks.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma binaryProbability_cyclotomic_residue_bound (m : ℕ) {k : ℕ} (hk : 0 < k) :
    binaryProbability m (fun p ↦ cyclotomic k ℤ ∣ p) ≤
      (4 / Real.sqrt (((m : ℝ) + 1) / k)) ^ k.totient := by
  letI : DecidablePred (fun r : Fin k ↦ r.val < k.totient) :=
    fun _ ↦ Classical.propDecidable _
  let α := fun r : Fin k ↦ {i : Fin m // residueIndex hk i = r} → Bool
  let e : (Fin m → Bool) ≃ (∀ r, α r) := groupWordEquiv (residueIndex hk)
  let E := fun w : ∀ r, α r ↦ cyclotomic k ℤ ∣ wordPolynomial (e.symm w)
  let c : ℝ := 4 / Real.sqrt (((m : ℝ) + 1) / k)
  have hunique (v w : ∀ r, α r) (hv : E v) (hw : E w)
      (hhigh : ∀ r : Fin k, ¬r.val < k.totient → v r = w r) :
      ∀ r : Fin k, r.val < k.totient →
        residueBlockCoefficient m hk r (v r) = residueBlockCoefficient m hk r (w r) := by
    have hpoly := cyclotomic_dvd_determines_low_residue_coefficients hk
      (e.symm v) (e.symm w) hv hw (fun r hr ↦ by
        change (wordResiduePolynomial k ((groupWordEquiv (residueIndex hk)).symm v)).coeff r.val =
          (wordResiduePolynomial k ((groupWordEquiv (residueIndex hk)).symm w)).coeff r.val
        rw [coeff_wordResiduePolynomial_grouped, coeff_wordResiduePolynomial_grouped,
          hhigh r (by omega)])
    intro r _
    have heq := congrArg (fun p : ℤ[X] ↦ p.coeff r.val) hpoly
    simpa only [e, coeff_wordResiduePolynomial_grouped] using heq
  calc
    _ = uniformProbability E := by
      exact (uniformProbability_equiv e.symm
        (fun w : Fin m → Bool ↦ cyclotomic k ℤ ∣ wordPolynomial w)).symm
    _ ≤ ∏ r : {r : Fin k // r.val < k.totient}, c := by
      exact uniformProbability_selected_coordinates_le
        (fun r : Fin k ↦ r.val < k.totient) E
        (fun r ↦ residueBlockCoefficient m hk r) (fun _ ↦ c)
        (fun _ _ ↦ by dsimp [c]; positivity)
        (fun r _ z ↦ uniformProbability_residueBlockCoefficient_le m hk r z) hunique
    _ = _ := by
      let er : {r : Fin k // r.val < k.totient} ≃ Fin k.totient :=
        { toFun := fun r ↦ ⟨r.val.val, r.property⟩
          invFun := fun r ↦ ⟨⟨r.val, lt_of_lt_of_le r.isLt (Nat.totient_le k)⟩, r.isLt⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_congr er, Fintype.card_fin]

lemma binaryProbability_cyclotomic_residue_bound_degree {n k : ℕ}
    (hn : 1 ≤ n) (hk : 0 < k) :
    binaryProbability (n - 1) (fun p ↦ cyclotomic k ℤ ∣ p) ≤
      (4 / Real.sqrt ((n : ℝ) / k)) ^ k.totient := by
  have hnR : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel hn
  simpa only [hnR] using binaryProbability_cyclotomic_residue_bound (n - 1) hk

end OdlyzkoPoonen
