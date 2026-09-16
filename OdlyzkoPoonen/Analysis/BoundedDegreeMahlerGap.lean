import OdlyzkoPoonen.Analysis.IntegerMahlerMeasure

/-!
# A positive Mahler gap in each bounded degree

Northcott finiteness gives a positive logarithmic gap above measure one for
integer polynomials of bounded degree. The constant depends on the degree
bound. This handles finite low-degree exceptions in a quantitative theorem;
it cannot replace the required uniform estimate as the degree tends to infinity.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped NNReal

lemma exists_pos_le_on_finite {α : Type*} {s : Set α} (hs : s.Finite)
    (f : α → ℝ) (hpos : ∀ a ∈ s, 0 < f a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ s, ε ≤ f a := by
  by_cases hn : s.Nonempty
  · obtain ⟨a, ha, hmin⟩ := Set.exists_min_image s f hs hn
    exact ⟨f a, hpos a ha, hmin⟩
  · exact ⟨1, zero_lt_one, fun a ha ↦ (hn ⟨a, ha⟩).elim⟩

lemma exists_pos_log_mahler_gap_bounded_degree (d : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ J : ℤ[X], J.natDegree ≤ d →
      1 < (J.map (Int.castRingHom ℂ)).mahlerMeasure →
      ε ≤ Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  let s : Set ℤ[X] := {J | J.natDegree ≤ d ∧
    (J.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2 ∧
      1 < (J.map (Int.castRingHom ℂ)).mahlerMeasure}
  have hs : s.Finite := (finite_mahlerMeasure_le d (2 : ℝ≥0)).subset
    (fun J h ↦ ⟨h.1, h.2.1⟩)
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_on_finite hs
    (fun J ↦ Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure)
    (fun _ h ↦ Real.log_pos h.2.2)
  refine ⟨min δ (Real.log 2), lt_min hδ (Real.log_pos (by norm_num)), ?_⟩
  intro J hdeg hM
  by_cases hsmall : (J.map (Int.castRingHom ℂ)).mahlerMeasure ≤ 2
  · exact (min_le_left _ _).trans (hδle J ⟨hdeg, hsmall, hM⟩)
  · exact (min_le_right _ _).trans (Real.log_le_log (by norm_num) (le_of_not_ge hsmall))

lemma exists_pos_noncyclotomic_log_mahler_gap_bounded_degree (d : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ J : ℤ[X], 0 < J.natDegree → J.natDegree ≤ d →
      (¬ X ∣ J) → (¬ HasCyclotomicDivisor J) →
      ε ≤ Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨ε, hε, hgap⟩ := exists_pos_log_mahler_gap_bounded_degree d
  exact ⟨ε, hε, fun J hpos hdeg hX hcyc ↦
    hgap J hdeg (one_lt_mahlerMeasure_of_no_cyclotomic hpos hX hcyc)⟩

end OdlyzkoPoonen
