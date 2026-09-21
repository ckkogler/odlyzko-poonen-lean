import OdlyzkoPoonen.ModFour.CompanionProbability
import OdlyzkoPoonen.Probability.ReciprocalLaw
import OdlyzkoPoonen.Combinatorics.FiberCounting

/-!
# Counting reciprocal products of binary polynomials

Reversal preserves the reciprocal product. Away from the exceptional companion
event its fibers have at most two elements. The two resulting counting bounds
keep the exact correction for polynomials fixed by reversal.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical

noncomputable def binaryAutocorrelationFamily (m : ℕ) : Finset ℤ[X] :=
  (binaryFamily m).image autocorrelation

lemma card_reciprocal_binaryFamily (m : ℕ) :
    ((binaryFamily m).filter (fun p ↦ p.reverse = p)).card = 2 ^ ((m + 1) / 2) := by
  classical
  have he : ((f2Family m).filter (fun p ↦ p.reverse = p)).image zeroOneLift =
      (binaryFamily m).filter (fun p ↦ p.reverse = p) := by
    ext p
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨q, ⟨hq, hr⟩, rfl⟩
      refine ⟨mem_binaryFamily_iff.mpr (mem_f2Family_iff.mp hq).lift, ?_⟩
      rw [← zeroOneLift_reverse, hr]
    · rintro ⟨hp, hr⟩
      have hb := (mem_binaryFamily_iff.mp hp).binary
      refine ⟨reducePolynomial 2 p, ⟨mem_f2Family_iff.mpr
        (mem_binaryFamily_iff.mp hp).reduce, ?_⟩, zeroOneLift_reduce hb⟩
      rw [← hb.reduce_reverse, hr]
  rw [← he, Finset.card_image_of_injective _ zeroOneLift_injective]
  exact card_reciprocal_f2Family m

theorem binaryAutocorrelationFamily_card_upper (m : ℕ) :
    2 * (binaryAutocorrelationFamily m).card ≤ 2 ^ m + 2 ^ ((m + 1) / 2) := by
  classical
  have h := twice_image_card_le_card_add_fixed (binaryFamily m) autocorrelation
    Polynomial.reverse
    (fun p hp ↦ mem_binaryFamily_iff.mpr (mem_binaryFamily_iff.mp hp).reverse)
    (fun p hp ↦ autocorrelation_reverse (by
      rw [(mem_binaryFamily_iff.mp hp).constant]
      exact one_ne_zero))
  simpa only [binaryAutocorrelationFamily, card_binaryFamily,
    card_reciprocal_binaryFamily] using h

lemma companion_free_fiber_card_le_two (m : ℕ) (y : ℤ[X])
    (hy : y ∈ ((binaryFamily m).filter
      (fun p ↦ ¬ HasModFourCompanion (m + 1) p)).image autocorrelation) :
    (((binaryFamily m).filter (fun p ↦ ¬ HasModFourCompanion (m + 1) p)).filter
      (fun p ↦ autocorrelation p = y)).card ≤ 2 := by
  classical
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
  have hsub : (((binaryFamily m).filter
      (fun q ↦ ¬ HasModFourCompanion (m + 1) q)).filter
      (fun q ↦ autocorrelation q = autocorrelation p)) ⊆ {p, p.reverse} := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqB := (Finset.mem_filter.mp hq'.1).1
    by_cases hqp : q = p
    · simp [hqp]
    by_cases hqr : q = p.reverse
    · simp [hqr]
    exact False.elim ((Finset.mem_filter.mp hp).2
      ⟨q, mem_binaryFamily_iff.mp hqB, hqp, hqr, by
        unfold CongruentMod
        rw [hq'.2]⟩)
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem binaryAutocorrelationFamily_card_lower (m : ℕ) :
    (2 : ℝ) ^ m * (1 - binaryProbability m (HasModFourCompanion (m + 1))) ≤
      2 * ((binaryAutocorrelationFamily m).card : ℝ) := by
  classical
  let good := (binaryFamily m).filter (fun p ↦ ¬ HasModFourCompanion (m + 1) p)
  let bad := (binaryFamily m).filter (HasModFourCompanion (m + 1))
  have hgood : good.card ≤ 2 * (binaryAutocorrelationFamily m).card := by
    have h := card_le_twice_image_of_fibers good autocorrelation
      (companion_free_fiber_card_le_two m)
    apply h.trans
    apply Nat.mul_le_mul_left
    apply Finset.card_le_card
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  have htotal : bad.card + good.card = 2 ^ m := by
    dsimp [bad, good]
    rw [Finset.card_filter_add_card_filter_not, card_binaryFamily]
  have htotalR : (bad.card : ℝ) + good.card = (2 : ℝ) ^ m := by exact_mod_cast htotal
  have hgoodR : (good.card : ℝ) ≤ 2 * ((binaryAutocorrelationFamily m).card : ℝ) := by
    exact_mod_cast hgood
  rw [binaryProbability_eq_count]
  change (2 : ℝ) ^ m * (1 - (bad.card : ℝ) / (2 : ℝ) ^ m) ≤ _
  have hpow : (2 : ℝ) ^ m ≠ 0 := by positivity
  have he : (2 : ℝ) ^ m * (1 - (bad.card : ℝ) / (2 : ℝ) ^ m) =
      (2 : ℝ) ^ m - bad.card := by field_simp
  rw [he]
  linarith

end OdlyzkoPoonen
