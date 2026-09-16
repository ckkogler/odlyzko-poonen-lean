import OdlyzkoPoonen.FiniteField.FactorEndpoints
import OdlyzkoPoonen.Probability.ReciprocalLaw

/-!
# Endpoint families indexed by polynomial degree

Unlike `f2Family`, whose parameter counts internal bits, `f2EndpointFamily h`
contains precisely the monic degree-`h` polynomials with constant one. Degree
zero is the singleton `{1}`. This convention allows quotient counting to include
constant quotients without a separate random-word model.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped Classical

/-- The actual endpoint-one family of degree `h`, including degree zero. -/
noncomputable def f2EndpointFamily (h : ℕ) : Finset (ZMod 2)[X] :=
  if h = 0 then {1} else f2Family (h - 1)

lemma mem_f2EndpointFamily_iff {h : ℕ} {p : (ZMod 2)[X]} :
    p ∈ f2EndpointFamily h ↔ HasF2Endpoints h p := by
  cases h with
  | zero =>
    simp only [f2EndpointFamily, ite_true, Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨monic_one, natDegree_one, coeff_one_zero⟩
    · exact HasF2Endpoints.eq_one_of_degree_zero
  | succ n =>
    simp only [f2EndpointFamily, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one]
    exact mem_f2Family_iff

lemma card_f2EndpointFamily (h : ℕ) :
    (f2EndpointFamily h).card = if h = 0 then 1 else 2 ^ (h - 1) := by
  by_cases hh : h = 0
  · simp [f2EndpointFamily, hh]
  · simp only [f2EndpointFamily, ite_eq_right hh, card_f2Family]

lemma f2EndpointFamily_nonempty (h : ℕ) : (f2EndpointFamily h).Nonempty := by
  rw [← Finset.card_pos, card_f2EndpointFamily]
  split_ifs <;> positivity

lemma card_f2EndpointFamily_le (h : ℕ) : (f2EndpointFamily h).card ≤ 2 ^ h := by
  rw [card_f2EndpointFamily]
  split_ifs with hh
  · simp [hh]
  · exact Nat.pow_le_pow_right (by omega) (Nat.sub_le h 1)

lemma card_reciprocal_f2EndpointFamily (h : ℕ) :
    ((f2EndpointFamily h).filter (fun p ↦ p.reverse = p)).card = 2 ^ (h / 2) := by
  cases h with
  | zero =>
    have hr : (1 : (ZMod 2)[X]).reverse = 1 := by
      simpa only [C_1] using Polynomial.reverse_C (1 : ZMod 2)
    have hf : ((f2EndpointFamily 0).filter (fun p ↦ p.reverse = p)) = {1} := by
      ext p
      simp only [Finset.mem_filter, f2EndpointFamily, ite_true, Finset.mem_singleton]
      exact ⟨fun hp ↦ hp.1, fun hp ↦ ⟨hp, by simpa only [hp] using hr⟩⟩
    rw [hf]
    norm_num
  | succ n =>
    simpa only [f2EndpointFamily, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one]
      using card_reciprocal_f2Family n

end OdlyzkoPoonen
