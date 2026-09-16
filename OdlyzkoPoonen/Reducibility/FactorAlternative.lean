import OdlyzkoPoonen.Polynomial.RationalReducibility
import OdlyzkoPoonen.Polynomial.FactorReversal
import OdlyzkoPoonen.ModFour.CompanionReduction
import OdlyzkoPoonen.Probability.ReciprocalIntegerDivisors

/-!
# The companion-or-reciprocal alternative

Gauss's lemma produces two nonconstant monic integer factors. If either factor
is reciprocal it is the required divisor. Otherwise reversing the second factor
produces an actual distinct binary companion. Its autocorrelation is equal over
the integers, which implies the required congruence modulo four.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma HasBinaryEndpoints.companion_or_reciprocal_of_reducible {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hn : 1 ≤ n) (hred : ReducibleOverRat p) :
    HasModFourCompanion n p ∨ HasLargeReciprocalIntegerDivisor 1 p := by
  obtain ⟨a, b, ha, hb, hab, had, hbd⟩ := hp.monic_factors_of_reducible hn hred
  by_cases har : a = a.reverse
  · exact Or.inr ⟨a, ha, ⟨b, hab⟩, har.symm, had⟩
  by_cases hbr : b = b.reverse
  · exact Or.inr ⟨b, hb, ⟨a, by rw [hab, mul_comm]⟩, hbr.symm, hbd⟩
  obtain ⟨_, _, hq, hcorr, heq, hrev⟩ := binary_factor_reversal hp ha hb hab
  refine Or.inl ⟨a * b.reverse, hq, ?_, ?_, ?_⟩
  · exact fun h ↦ hbr (heq.mp h)
  · exact fun h ↦ har (hrev.mp h)
  · change reducePolynomial 4 (autocorrelation p) = reducePolynomial 4 (autocorrelation (a * b.reverse))
    exact congrArg (reducePolynomial 4) hcorr.symm

end OdlyzkoPoonen
