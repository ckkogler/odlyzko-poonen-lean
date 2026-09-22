import OdlyzkoPoonen.Asymptotics.Reducibility

/-!
# Main results for random binary polynomials

Combine the irreducibility limit and sharp leading reducibility asymptotic into
one statement corresponding to Theorem 1.1. The factorization and companion
bounds are supplied directly by their existing proof modules.
-/

namespace OdlyzkoPoonen
open Filter Asymptotics
open scoped Topology

/-- Rational irreducibility tends to probability one, and reducibility equals
`sqrt(2/(pi*n))` up to an error of order `1/n`. -/
theorem irreducibility_and_reducibility_asymptotic :
    Tendsto (fun n : ℕ ↦ binaryProbability (n - 1)
      (fun P ↦ Irreducible (P.map (Int.castRingHom ℚ)))) atTop (𝓝 1) ∧
    ((fun n : ℕ ↦ binaryProbability (n - 1) ReducibleOverRat -
      Real.sqrt (2 / (Real.pi * (n : ℝ)))) =O[atTop]
        (fun n : ℕ ↦ 1 / (n : ℝ))) :=
  ⟨odlyzko_poonen_irreducibility, binaryProbability_reducible_asymptotic⟩

end OdlyzkoPoonen
