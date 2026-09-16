import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

/-!
# Separated root powers force large Mahler measure

Suppose the roots of a monic polynomial `J` are simple and remain distinct after
raising them to the power `q`. If `J` divides `R(X^q)`, those powers occur in
`R` with at least their required multiplicities. The product formula gives
`M(J)^q ≤ M(R)` when the leading coefficient of `R` has norm at least one.
This is the analytic inequality for the sparse-word argument; root separation
is an explicit intermediate hypothesis, to be discharged arithmetically later.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma max_one_norm_pow (z : ℂ) (q : ℕ) :
    max 1 ‖z ^ q‖ = (max 1 ‖z‖) ^ q := by
  rw [norm_pow]
  by_cases h : ‖z‖ ≤ 1
  · rw [max_eq_left h, max_eq_left (pow_le_one₀ (norm_nonneg z) h), one_pow]
  · have h' : 1 ≤ ‖z‖ := le_of_not_ge h
    rw [max_eq_right h', max_eq_right (one_le_pow₀ h')]

lemma prod_max_one_norm_mono {s t : Multiset ℂ} (hst : s ≤ t) :
    (s.map (fun z ↦ max 1 ‖z‖)).prod ≤ (t.map (fun z ↦ max 1 ‖z‖)).prod := by
  obtain ⟨u, rfl⟩ := exists_add_of_le hst
  rw [Multiset.map_add, Multiset.prod_add]
  exact le_mul_of_one_le_right
    (Multiset.prod_map_nonneg (fun _ _ ↦ (by positivity)))
    (Multiset.one_le_prod_map (fun z _ ↦ le_max_left 1 ‖z‖))

lemma roots_pow_le_of_dvd_expand {J R : ℂ[X]} {q : ℕ}
    (hJ : J ≠ 0) (hR : R ≠ 0) (hsimple : J.roots.Nodup)
    (hsep : ∀ z ∈ J.roots, ∀ w ∈ J.roots, z ^ q = w ^ q → z = w)
    (hdvd : J ∣ expand ℂ q R) :
    J.roots.map (fun z ↦ z ^ q) ≤ R.roots := by
  apply (Multiset.le_iff_subset (Multiset.Nodup.map_on hsep hsimple)).mpr
  intro a ha
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ha
  apply (mem_roots hR).mpr
  have hzero := ((mem_roots hJ).mp hz).dvd hdvd
  simpa only [IsRoot.def, expand_eval] using hzero

lemma mahlerMeasure_pow_le_of_dvd_expand {J R : ℂ[X]} (q : ℕ)
    (hJ : J.Monic) (hR : 1 ≤ ‖R.leadingCoeff‖) (hsimple : J.roots.Nodup)
    (hsep : ∀ z ∈ J.roots, ∀ w ∈ J.roots, z ^ q = w ^ q → z = w)
    (hdvd : J ∣ expand ℂ q R) :
    J.mahlerMeasure ^ q ≤ R.mahlerMeasure := by
  have hR0 : R ≠ 0 := by intro h; norm_num [h] at hR
  have hle := roots_pow_le_of_dvd_expand hJ.ne_zero hR0 hsimple hsep hdvd
  calc
    J.mahlerMeasure ^ q = (J.roots.map (fun z ↦ max 1 ‖z ^ q‖)).prod := by
      rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hJ.leadingCoeff, norm_one,
        one_mul]
      simp_rw [max_one_norm_pow]
      exact Multiset.prod_map_pow.symm
    _ = ((J.roots.map (fun z ↦ z ^ q)).map (fun z ↦ max 1 ‖z‖)).prod := by
      simp only [Multiset.map_map, Function.comp_def]
    _ ≤ (R.roots.map (fun z ↦ max 1 ‖z‖)).prod := prod_max_one_norm_mono hle
    _ ≤ R.mahlerMeasure :=
      prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff hR

end OdlyzkoPoonen
