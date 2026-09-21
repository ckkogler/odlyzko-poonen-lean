import OdlyzkoPoonen.Asymptotics.PeriodicMonicExpansion
import OdlyzkoPoonen.Analysis.PeriodicExpansionSums
import OdlyzkoPoonen.Probability.FiniteInclusionExclusion
import OdlyzkoPoonen.Polynomial.CyclotomicProducts

/-!
# Periodic expansions for finite cyclotomic unions

Inclusion-exclusion reduces a finite union to products of distinct cyclotomic
polynomials. A common multiple of the orders supplies one residue modulus for
all intersections and therefore for the union.
-/

namespace OdlyzkoPoonen
open Polynomial Filter Asymptotics
open scoped BigOperators Classical

lemma binaryProbability_cyclotomic_union_inclusion_exclusion (m : ℕ) (s : Finset ℕ)
    (hs : ∀ k ∈ s, 0 < k) :
    binaryProbability m (fun p ↦ ∃ k ∈ s, cyclotomic k ℤ ∣ p) =
      ∑ t : s.powerset.filter (·.Nonempty), (-1 : ℝ) ^ (t.val.card + 1) *
        binaryProbability m (fun p ↦ cyclotomicProduct t.val ∣ p) := by
  unfold binaryProbability
  rw [uniformProbability_finite_union]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  congr 1
  funext w
  apply propext
  exact (cyclotomicProduct_dvd_iff
    (fun k hk ↦ hs k ((Finset.mem_powerset.mp (Finset.mem_filter.mp t.property).1) hk))
    (wordPolynomial w)).symm

/-- Every finite union of cyclotomic divisors other than `X-1` has the expansion. -/
theorem binaryProbability_cyclotomic_union_expansion (s : Finset ℕ)
    (hs : ∀ k ∈ s, 2 ≤ k) {q : ℕ} (hq : 0 < q) (horders : ∀ k ∈ s, k ∣ q)
    (R : ℕ) (hR : 1 ≤ R) :
    ∃ c : Fin (2 * q) → ℕ → ℝ, (∀ r, c r 0 = 0) ∧
      (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ ∃ k ∈ s, cyclotomic k ℤ ∣ p) -
        ∑ j ∈ Finset.range (2 * R), c ⟨(n - 1) % (2 * q), Nat.mod_lt _ (by omega)⟩ j *
          (n : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop]
            (fun n : ℕ ↦ (n : ℝ) ^ (-(R : ℝ))) := by
  have hex (t : s.powerset.filter (·.Nonempty)) :
      ∃ c : Fin (2 * q) → ℕ → ℝ, (∀ r, c r 0 = 0) ∧
        (fun n : ℕ ↦ binaryProbability (n - 1) (fun p ↦ cyclotomicProduct t.val ∣ p) -
          ∑ j ∈ Finset.range (2 * R), c ⟨(n - 1) % (2 * q), Nat.mod_lt _ (by omega)⟩ j *
            (n : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop]
              (fun n : ℕ ↦ (n : ℝ) ^ (-(R : ℝ))) := by
    have ht := Finset.mem_filter.mp t.property
    have hts : t.val ⊆ s := Finset.mem_powerset.mp ht.1
    have hpos : ∀ k ∈ t.val, 0 < k := fun k hk ↦ lt_of_lt_of_le (by omega) (hs k (hts hk))
    apply degreeProbability_monic_residue_expansion (cyclotomicProduct_monic t.val)
      ?_ hq (cyclotomicProduct_dvd_X_pow_sub_one hq (fun k hk ↦ horders k (hts hk)))
      (cyclotomicProduct_dvd_geom_sum hq (fun k hk ↦ horders k (hts hk)) ?_) R hR
    · rw [cyclotomicProduct_natDegree]
      exact Finset.sum_pos (fun k hk ↦ Nat.totient_pos.mpr (hpos k hk)) ht.2
    · intro hone
      have := hs 1 (hts hone)
      omega
  choose c hc0 hc using hex
  obtain ⟨b, hb0, hb⟩ := finite_sum_periodic_half_expansion (by omega : 0 < 2 * q)
    (fun t : s.powerset.filter (·.Nonempty) ↦
      fun n ↦ binaryProbability (n - 1) (fun p ↦ cyclotomicProduct t.val ∣ p))
    (fun t ↦ (-1 : ℝ) ^ (t.val.card + 1)) c hc0 hc
  refine ⟨b, hb0, ?_⟩
  simpa only [binaryProbability_cyclotomic_union_inclusion_exclusion _ s
    (fun k hk ↦ lt_of_lt_of_le (by omega) (hs k hk))] using hb

end OdlyzkoPoonen
