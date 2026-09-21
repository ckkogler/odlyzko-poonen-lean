import OdlyzkoPoonen.Analysis.ResidueClassBounds

/-!
# Finite linear combinations of periodic half-power expansions

A common residue modulus permits finite linear combinations without changing
the error order. The coefficients are the corresponding linear combinations.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem finite_sum_periodic_half_expansion {q R : ℕ} (hq : 0 < q)
    (F : ι → ℕ → ℝ) (a : ι → ℝ) (c : ι → Fin q → ℕ → ℝ)
    (hc0 : ∀ i r, c i r 0 = 0)
    (hF : ∀ i, (fun n : ℕ ↦ F i n -
      ∑ j ∈ Finset.range (2 * R), c i ⟨(n - 1) % q, Nat.mod_lt _ hq⟩ j *
        (n : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-(R : ℝ)))) :
    ∃ b : Fin q → ℕ → ℝ, (∀ r, b r 0 = 0) ∧
      (fun n : ℕ ↦ (∑ i, a i * F i n) -
        ∑ j ∈ Finset.range (2 * R), b ⟨(n - 1) % q, Nat.mod_lt _ hq⟩ j *
          (n : ℝ) ^ (-(j : ℝ) / 2)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-(R : ℝ))) := by
  let b : Fin q → ℕ → ℝ := fun r j ↦ ∑ i, a i * c i r j
  refine ⟨b, ?_, ?_⟩
  · intro r
    simp [b, hc0]
  · have he := Asymptotics.IsBigO.sum (s := Finset.univ)
      (fun i _ ↦ (hF i).const_mul_left (a i))
    have halg (n : ℕ) :
        (∑ i, a i * (F i n - ∑ j ∈ Finset.range (2 * R),
          c i ⟨(n - 1) % q, Nat.mod_lt _ hq⟩ j * (n : ℝ) ^ (-(j : ℝ) / 2))) =
        (∑ i, a i * F i n) - ∑ j ∈ Finset.range (2 * R),
          b ⟨(n - 1) % q, Nat.mod_lt _ hq⟩ j * (n : ℝ) ^ (-(j : ℝ) / 2) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp only [b, Finset.sum_mul, mul_assoc]
    convert! he using 1
    funext n
    simpa only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply] using (halg n).symm

end OdlyzkoPoonen
