import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

/-!
# Galois conjugacy of polynomial roots and primitive roots of unity

All normality hypotheses concern algebraic extensions. In particular this
module never assumes that the whole field of complex numbers is normal over
`ℚ`. Later applications take the splitting field of the polynomial.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma root_ne_zero_of_constant_ne_zero {F K : Type*} [Field F] [Field K]
    [Algebra F K] {P : F[X]} (hP : P.coeff 0 ≠ 0) {x : K}
    (hx : x ∈ P.rootSet K) : x ≠ 0 := by
  intro hx0
  have he := aeval_eq_zero_of_mem_rootSet hx
  rw [hx0] at he
  apply hP
  apply (algebraMap F K).injective
  rw [map_zero, coeff_zero_eq_aeval_zero']
  exact he

lemma exists_algEquiv_map_root {F K : Type*} [Field F] [Field K]
    [Algebra F K] [Normal F K] {P : F[X]} (hmonic : P.Monic)
    (hirr : Irreducible P) {x y : K} (hx : x ∈ P.rootSet K)
    (hy : y ∈ P.rootSet K) : ∃ σ : K ≃ₐ[F] K, σ x = y := by
  apply minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic y)
  rw [← minpoly.eq_of_irreducible_of_monic hirr
    (aeval_eq_zero_of_mem_rootSet hy) hmonic]
  exact aeval_eq_zero_of_mem_rootSet hx

lemma algEquiv_map_mem_rootSet {F K : Type*} [Field F] [Field K]
    [Algebra F K] {P : F[X]} (σ : K ≃ₐ[F] K) {x : K}
    (hx : x ∈ P.rootSet K) : σ x ∈ P.rootSet K :=
  rootSet_mapsTo σ.toAlgHom hx

lemma exists_algEquiv_map_primitiveRoot {K : Type*} [Field K] [CharZero K]
    [Normal ℚ K] {r : ℕ} (hr : 0 < r) {x y : K}
    (hx : IsPrimitiveRoot x r) (hy : IsPrimitiveRoot y r) :
    ∃ σ : K ≃ₐ[ℚ] K, σ x = y := by
  apply minpoly.exists_algEquiv_of_root (Algebra.IsAlgebraic.isAlgebraic y)
  rw [← cyclotomic_eq_minpoly_rat hy hr, cyclotomic_eq_minpoly_rat hx hr]
  exact minpoly.aeval ℚ x

lemma rootSet_nonempty_of_splits_of_irreducible {F K : Type*} [Field F] [Field K]
    [Algebra F K] {P : F[X]} (hmonic : P.Monic) (hirr : Irreducible P)
    (hsplit : (P.map (algebraMap F K)).Splits) : (P.rootSet K).Nonempty := by
  have hdegree : (P.map (algebraMap F K)).natDegree ≠ 0 := by
    rw [natDegree_map_eq_of_injective (algebraMap F K).injective]
    exact hirr.natDegree_pos.ne'
  obtain ⟨x, hx⟩ := hsplit.exists_eval_eq_zero (degree_ne_of_natDegree_ne hdegree)
  refine ⟨x, hmonic.mem_rootSet.mpr ?_⟩
  simpa only [eval_map, aeval_def] using hx

end OdlyzkoPoonen
