import OdlyzkoPoonen.ModFour.Parity
import OdlyzkoPoonen.FiniteField.OuterAgreement
import OdlyzkoPoonen.FiniteField.PairedPolynomial
import OdlyzkoPoonen.Probability.FreshBitConstraints

/-!
# Prefix dependence of the actual discrepancy

The factor-pair discrepancy at index `k` is determined by the opposite factor
coefficients through `k`. In paired coordinates these use exactly the lower
bits through that index, together with the fixed pair sums. The central bit
has no effect. This discharges the locality hypothesis of fresh-bit counting.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma autocorrelationDiscrepancy_eq_of_outer {d e k : ℕ} {a b b' : (ZMod 2)[X]}
    (h : AgreeOnOuter e k b b') (ha : HasF2Endpoints d a)
    (hb : HasF2Endpoints e b) (hb' : HasF2Endpoints e b') (hk : k ≤ e) :
    autocorrelationDiscrepancy a b k = autocorrelationDiscrepancy a b' k := by
  have hP := (h.mul_left ha hb hb' hk).zeroOneLift.autocorrelation
    (ha.mul hb).lift.degree (ha.mul hb').lift.degree (show k ≤ d + e by omega)
  have hQ := ((h.reverse hb hb' hk).mul_left ha hb.reverse hb'.reverse hk).zeroOneLift.autocorrelation
    (ha.mul hb.reverse).lift.degree (ha.mul hb'.reverse).lift.degree (show k ≤ d + e by omega)
  unfold autocorrelationDiscrepancy halfCoefficientDifference
  rw [hP, hQ]

lemma pairedPolynomial_agreeOnOuter {n : ℕ} {u u' c : Fin (n / 2) → Bool}
    (z z' : Fin (n % 2) → Bool) {i : Fin (n / 2)}
    (h : ∀ j ≤ i, u j = u' j) :
    AgreeOnOuter (n + 1) (i.val + 1) (pairedPolynomial u c z) (pairedPolynomial u' c z') := by
  have hp := pairedPolynomial_endpoints u c z
  have hq := pairedPolynomial_endpoints u' c z'
  constructor
  · intro k hk
    by_cases hk0 : k = 0
    · rw [hk0, hp.constant, hq.constant]
    · let j : Fin (n / 2) := ⟨k - 1, by have := i.isLt; omega⟩
      have hj : j.val + 1 = k := by dsimp [j]; omega
      have hji : j ≤ i := by change j.val ≤ i.val; dsimp [j]; omega
      rw [← hj, coeff_pairedPolynomial_lower, coeff_pairedPolynomial_lower, h j hji]
  · intro k hk
    by_cases hk0 : k = 0
    · simp only [hk0, Nat.sub_zero, hp.coeff_degree, hq.coeff_degree]
    · let j : Fin (n / 2) := ⟨k - 1, by have := i.isLt; omega⟩
      have hj : j.val + 1 = k := by dsimp [j]; omega
      have hji : j ≤ i := by change j.val ≤ i.val; dsimp [j]; omega
      rw [← hj, coeff_pairedPolynomial_upper, coeff_pairedPolynomial_upper, h j hji]

/-- The actual discrepancy bit, in the Boolean coordinates used for counting. -/
noncomputable def pairedDiscrepancy {n : ℕ} (a : (ZMod 2)[X])
    (c : Fin (n / 2) → Bool) (z : Fin (n % 2) → Bool)
    (u : Fin (n / 2) → Bool) (i : Fin (n / 2)) : Bool :=
  f2ToBit (autocorrelationDiscrepancy a (pairedPolynomial u c z) (i.val + 1))

lemma pairedDiscrepancy_eq_of_prefix {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) {u u' c : Fin (n / 2) → Bool}
    (z z' : Fin (n % 2) → Bool) {i : Fin (n / 2)} (h : ∀ j ≤ i, u j = u' j) :
    pairedDiscrepancy a c z u i = pairedDiscrepancy a c z' u' i := by
  apply congrArg f2ToBit
  exact autocorrelationDiscrepancy_eq_of_outer (pairedPolynomial_agreeOnOuter z z' h)
    ha (pairedPolynomial_endpoints u c z) (pairedPolynomial_endpoints u' c z')
    (by have := i.isLt; omega)

lemma pairedDiscrepancy_dependsOnPrefix {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (c : Fin (n / 2) → Bool) (z : Fin (n % 2) → Bool) :
    DependsOnPrefix (pairedDiscrepancy a c z) := by
  intro i u u' h
  exact pairedDiscrepancy_eq_of_prefix ha z z h

lemma pairedDiscrepancy_center_independent {d n : ℕ} {a : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (c u : Fin (n / 2) → Bool)
    (z z' : Fin (n % 2) → Bool) : pairedDiscrepancy a c z u = pairedDiscrepancy a c z' u := by
  funext i
  exact pairedDiscrepancy_eq_of_prefix ha z z' (fun _ _ ↦ rfl)

end OdlyzkoPoonen
