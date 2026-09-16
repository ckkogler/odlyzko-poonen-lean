import OdlyzkoPoonen.FiniteField.PairedPolynomial

/-!
# Reciprocity detected by opposite pairs

For an endpoint-one polynomial, agreement with its reverse is equivalent to
agreement of its lower and upper internal coefficient pairs. The central
coefficient needs no constraint. In the paired coordinates this says exactly
that the opposite-pair sum word is identically false.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma HasF2Endpoints.reverse_eq_iff_lower {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints (n + 1) p) :
    p.reverse = p ↔ ∀ i : Fin (n / 2), p.coeff (i.val + 1) = p.coeff (n + 1 - (i.val + 1)) := by
  constructor
  · intro h i
    have heq := congrArg (fun q : (ZMod 2)[X] ↦ q.coeff (i.val + 1)) h
    rw [coeff_reverse, hp.degree,
      revAt_le (show i.val + 1 ≤ n + 1 by have := i.isLt; omega)] at heq
    exact heq.symm
  · intro h
    apply f2WordPolynomial_ext hp.reverse hp
    intro j
    have hj := j.isLt
    rw [coeff_reverse, hp.degree, revAt_le (show j.val + 1 ≤ n + 1 by omega)]
    by_cases hl : j.val < n / 2
    · exact (h ⟨j.val, hl⟩).symm
    · by_cases hu : n - (j.val + 1) < n / 2
      · let i : Fin (n / 2) := ⟨n - (j.val + 1), hu⟩
        have hi : i.val + 1 = n + 1 - (j.val + 1) := by dsimp [i]; omega
        have hi' : n + 1 - (i.val + 1) = j.val + 1 := by dsimp [i]; omega
        have hh := h i
        rw [hi', hi] at hh
        exact hh
      · have hc : n + 1 - (j.val + 1) = j.val + 1 := by omega
        rw [hc]

lemma pairedPolynomial_reverse_eq_iff {n : ℕ} (u c : Fin (n / 2) → Bool)
    (z : Fin (n % 2) → Bool) :
    (pairedPolynomial u c z).reverse = pairedPolynomial u c z ↔ ∀ i, c i = false := by
  rw [(pairedPolynomial_endpoints u c z).reverse_eq_iff_lower]
  simp only [coeff_pairedPolynomial_lower, coeff_pairedPolynomial_upper]
  apply forall_congr'
  intro i
  cases c i <;> simp [bitToF2]

end OdlyzkoPoonen
