import OdlyzkoPoonen.Probability.FiniteUniform
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-!
# Inclusion-exclusion for finite uniform probabilities

The alternating sum over nonempty subfamilies is an exact identity of finite
cardinality ratios. It also holds for the empty sample-space convention.
-/

namespace OdlyzkoPoonen
open scoped BigOperators

variable {α ι : Type*} [Fintype α]

theorem uniformProbability_finite_union (s : Finset ι) (E : ι → α → Prop) :
    uniformProbability (fun a ↦ ∃ i ∈ s, E i a) =
      ∑ t : s.powerset.filter (·.Nonempty),
        (-1 : ℝ) ^ (t.val.card + 1) * uniformProbability (fun a ↦ ∀ i ∈ t.val, E i a) := by
  classical
  let S : ι → Finset α := fun i ↦ Finset.univ.filter (E i)
  have hu : s.biUnion S = Finset.univ.filter (fun a ↦ ∃ i ∈ s, E i a) := by
    ext a
    simp [S]
  have hi (t : s.powerset.filter (·.Nonempty)) :
      t.val.inf' (Finset.mem_filter.mp t.property).2 S =
        Finset.univ.filter (fun a ↦ ∀ i ∈ t.val, E i a) := by
    ext a
    simp [Finset.mem_inf', S]
  have he : ((s.biUnion S).card : ℝ) =
      ∑ t : s.powerset.filter (·.Nonempty), (-1 : ℝ) ^ (t.val.card + 1) *
        ((t.val.inf' (Finset.mem_filter.mp t.property).2 S).card : ℝ) := by
    exact_mod_cast Finset.inclusion_exclusion_card_biUnion s S
  rw [hu] at he
  simp_rw [hi] at he
  have hdiv := congrArg (fun x : ℝ ↦ x / Fintype.card α) he
  simp only [Finset.sum_div, mul_div_assoc] at hdiv
  convert hdiv using 1 <;> simp only [uniformProbability] <;> congr 2
  · congr 1
    ext a
    simp
  · funext t
    congr 4
    ext a
    simp

end OdlyzkoPoonen
