import OdlyzkoPoonen.Probability.FiniteEvents
import OdlyzkoPoonen.Polynomial.RationalReducibility

/-!
# Complements under the finite binary law

The word space is nonempty at every size, including zero internal bits. Its
actual counting law gives the exact complement identity for irreducibility.
-/

namespace OdlyzkoPoonen

lemma uniformProbability_not {α : Type*} [Fintype α] [Nonempty α] (E : α → Prop) :
    uniformProbability (fun a ↦ ¬ E a) = 1 - uniformProbability E := by
  have h := uniformProbability_sub_of_imp (fun _ : α ↦ True) E (fun _ _ ↦ trivial)
  simpa only [uniformProbability_true, true_and] using h.symm

lemma binaryProbability_irreducible_eq_one_sub_reducible (m : ℕ) :
    binaryProbability m (fun P ↦ Irreducible (P.map (Int.castRingHom ℚ))) =
      1 - binaryProbability m ReducibleOverRat := by
  simpa only [binaryProbability, ReducibleOverRat, not_not] using
    uniformProbability_not (fun w : Fin m → Bool ↦ ReducibleOverRat (wordPolynomial w))

end OdlyzkoPoonen
