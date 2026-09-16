import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

/-!
# Root-power polynomials via resultants

Reused from the completed Lp densities formalization (Constantin Kogler, 0BSD).
See `provenance/reused-source.json` for the source commit and content hashes.

The integer polynomial obtained by raising all roots to a common power.

The resultant Res_t(p(t), Y-t^k) has coefficients in the original coefficient
ring. Over the complex numbers it is leadingCoeff(p)^k times the product of
Y-z^k over the roots of p, with multiplicities. Its Mahler measure is therefore
exactly M(p)^k. This construction avoids assuming that algebraic numbers are
algebraic integers when bounding the Mahler measures of their powers.
-/

open Polynomial

namespace OdlyzkoPoonen

/-- Eliminate the original variable using Y-t^k. The outer variable of the
bivariate resultant is t, and its coefficients are polynomials in Y. -/
noncomputable def polynomialRootPowers {R : Type*} [CommRing R]
    (p : R[X]) (k : ℕ) : R[X] :=
  (p.map (Polynomial.C : R →+* R[X])).resultant
    (Polynomial.C (X : R[X]) - X ^ k) p.natDegree k

/-- The resultant factors over any domain in which the input splits. -/
theorem polynomialRootPowers_eq_prod_of_splits {R : Type*} [CommRing R] [IsDomain R]
    (p : R[X]) (hp : p.Splits) (k : ℕ) :
    polynomialRootPowers p k = C (p.leadingCoeff ^ k) *
      (p.roots.map (fun z ↦ X - C (z ^ k))).prod := by
  have hs := hp.map (Polynomial.C : R →+* R[X])
  have hd : (C (X : R[X]) - X ^ k).natDegree ≤ k := by
    exact (natDegree_sub_le _ _).trans (by simp)
  have h := resultant_eq_prod_eval (p.map (Polynomial.C : R →+* R[X]))
    (C (X : R[X]) - X ^ k) k hd hs
  rw [natDegree_map_eq_of_injective C_injective] at h
  rw [polynomialRootPowers, h]
  rw [leadingCoeff_map_of_injective C_injective,
    hp.roots_map_of_injective C_injective]
  simp only [← map_pow, Multiset.map_map, Function.comp_apply,
    eval_sub, eval_C, eval_pow, eval_X]

/-- The complex resultant factors with roots z^k and its original integer
leading coefficient raised to k. -/
theorem polynomialRootPowers_eq_prod (p : ℂ[X]) (k : ℕ) :
    polynomialRootPowers p k = C (p.leadingCoeff ^ k) *
      (p.roots.map (fun z ↦ X - C (z ^ k))).prod :=
  polynomialRootPowers_eq_prod_of_splits p (IsAlgClosed.splits p) k

theorem polynomialRootPowers_leadingCoeff_of_splits {R : Type*}
    [CommRing R] [IsDomain R] (p : R[X]) (hp : p.Splits) (k : ℕ) :
    (polynomialRootPowers p k).leadingCoeff = p.leadingCoeff ^ k := by
  rw [polynomialRootPowers_eq_prod_of_splits p hp k, leadingCoeff_mul, leadingCoeff_C,
    (monic_multiset_prod_of_monic p.roots (fun z ↦ X - C (z ^ k))
      (fun z _ ↦ monic_X_sub_C (z ^ k))).leadingCoeff, mul_one]

theorem polynomialRootPowers_natDegree_of_splits {K : Type*} [Field K]
    {p : K[X]} (hp : p ≠ 0) (hs : p.Splits) (k : ℕ) :
    (polynomialRootPowers p k).natDegree = p.natDegree := by
  rw [polynomialRootPowers_eq_prod_of_splits p hs k,
    natDegree_C_mul (pow_ne_zero k (leadingCoeff_ne_zero.mpr hp))]
  have he : p.roots.map (fun z ↦ X - C (z ^ k)) =
      (p.roots.map (fun z ↦ z ^ k)).map (fun z ↦ X - C z) := by
    rw [Multiset.map_map]
    rfl
  rw [he, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map,
    ← hs.natDegree_eq_card_roots]

/-- Divisibility after power substitution bounds the root-power resultant by
a power of the target polynomial. Repeated roots are counted with multiplicity. -/
theorem polynomialRootPowers_dvd_pow_of_dvd_comp {p q : ℂ[X]} (hp : p ≠ 0)
    (k : ℕ) (hd : p ∣ q.comp (X ^ k)) :
    polynomialRootPowers p k ∣ q ^ p.natDegree := by
  have hroot (z : ℂ) (hz : z ∈ p.roots) : X - C (z ^ k) ∣ q := by
    apply dvd_iff_isRoot.mpr
    have h := ((mem_roots hp).mp hz).dvd hd
    simpa only [IsRoot, eval_comp, eval_pow, eval_X] using h
  have hprod := Multiset.prod_dvd_prod_of_dvd
    (fun z : ℂ ↦ X - C (z ^ k)) (fun _ : ℂ ↦ q) hroot
  have hdiv : (p.roots.map (fun z ↦ X - C (z ^ k))).prod ∣ q ^ p.natDegree := by
    simpa only [Multiset.map_const', Multiset.prod_replicate,
      ← (IsAlgClosed.splits p).natDegree_eq_card_roots] using hprod
  rw [polynomialRootPowers_eq_prod]
  have hu : IsUnit (C (p.leadingCoeff ^ k)) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero k (leadingCoeff_ne_zero.mpr hp)))
  have hc : C (p.leadingCoeff ^ k) * (p.roots.map (fun z ↦ X - C (z ^ k))).prod ∣
      (p.roots.map (fun z ↦ X - C (z ^ k))).prod := by
    simpa using mul_dvd_mul (isUnit_iff_dvd_one.mp hu) (dvd_refl
      ((p.roots.map (fun z ↦ X - C (z ^ k))).prod))
  exact hc.trans hdiv

/-- Taking powers of all roots raises the genuine polynomial Mahler measure
to the same power. -/
theorem polynomialRootPowers_mahlerMeasure (p : ℂ[X]) (k : ℕ) :
    (polynomialRootPowers p k).mahlerMeasure = p.mahlerMeasure ^ k := by
  rw [polynomialRootPowers_eq_prod, Polynomial.mahlerMeasure_mul,
    Polynomial.mahlerMeasure_const, norm_pow,
    Polynomial.prod_mahlerMeasure_eq_mahlerMeasure_prod, Multiset.map_map]
  simp only [Function.comp_apply, Polynomial.mahlerMeasure_X_sub_C, norm_pow]
  have hm (z : ℂ) : max 1 (‖z‖ ^ k) = (max 1 ‖z‖) ^ k := by
    rcases le_total ‖z‖ 1 with hz | hz
    · rw [max_eq_left hz, one_pow, max_eq_left (pow_le_one₀ (norm_nonneg _) hz)]
    · rw [max_eq_right hz, max_eq_right (one_le_pow₀ hz)]
  simp_rw [hm]
  rw [Multiset.prod_map_pow, Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    mul_pow]

/-- Root-power resultants commute with an injective coefficient map, so their
complex factorizations describe actual integer-coefficient polynomials. -/
theorem polynomialRootPowers_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (p : R[X]) (k : ℕ) :
    (polynomialRootPowers p k).map φ = polynomialRootPowers (p.map φ) k := by
  unfold polynomialRootPowers
  change (Polynomial.mapRingHom φ)
    ((p.map C).resultant (C (X : R[X]) - X ^ k) p.natDegree k) = _
  rw [← resultant_map_map _ _ _ _ (Polynomial.mapRingHom φ),
    natDegree_map_eq_of_injective hφ]
  have hc : (Polynomial.mapRingHom φ).comp (Polynomial.C : R →+* R[X]) =
      (Polynomial.C : S →+* S[X]).comp φ := by
    ext a
    simp
  congr 1
  · rw [Polynomial.map_map, Polynomial.map_map, hc]
  · simp only [Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom]

/-- Every actual root z gives an actual root z^k of the resultant polynomial. -/
theorem polynomialRootPowers_isRoot {p : ℂ[X]} (hp : p ≠ 0)
    {z : ℂ} (hz : p.IsRoot z) (k : ℕ) :
    (polynomialRootPowers p k).IsRoot (z ^ k) := by
  apply dvd_iff_isRoot.mp
  rw [polynomialRootPowers_eq_prod]
  apply dvd_mul_of_dvd_right
  exact Multiset.dvd_prod (Multiset.mem_map.mpr ⟨z, (mem_roots hp).mpr hz, rfl⟩)

end OdlyzkoPoonen
