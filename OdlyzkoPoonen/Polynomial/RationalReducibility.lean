import OdlyzkoPoonen.Polynomial.Binary
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Reducibility over the rationals and integral monic factors

Reducibility means failure of the standard `Irreducible` predicate after the
ordinary coefficient map to the rationals. For a positive-degree monic integer
polynomial, Gauss's lemma gives a factorization into two positive-degree monic
integer polynomials. No extra condition on the factor coefficients is imposed.
-/

namespace OdlyzkoPoonen
open Polynomial

/-- Failure of irreducibility of the ordinary rational coefficient image. -/
def ReducibleOverRat (p : ℤ[X]) : Prop :=
  ¬ Irreducible (p.map (Int.castRingHom ℚ))

lemma monic_reducibleOverRat_iff {p : ℤ[X]} (hp : p.Monic) :
    ReducibleOverRat p ↔ ¬ Irreducible p := by
  unfold ReducibleOverRat
  exact not_congr (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp.isPrimitive).symm

lemma monic_factors_of_reducibleOverRat {p : ℤ[X]} (hp : p.Monic)
    (hdegree : 0 < p.natDegree) (hred : ReducibleOverRat p) :
    ∃ a b : ℤ[X], a.Monic ∧ b.Monic ∧ p = a * b ∧
      0 < a.natDegree ∧ 0 < b.natDegree := by
  classical
  have hn : p ≠ 1 := by
    intro he
    simp [he] at hdegree
  have hi := (monic_reducibleOverRat_iff hp).mp hred
  have hf : ¬ ∀ a b : ℤ[X], a.Monic → b.Monic → a * b = p →
      a.natDegree = 0 ∨ b.natDegree = 0 := by
    intro h
    exact hi (hp.irreducible_iff_natDegree.mpr ⟨hn, h⟩)
  push Not at hf
  obtain ⟨a, b, ha, hb, hab, had, hbd⟩ := hf
  exact ⟨a, b, ha, hb, hab.symm, Nat.pos_of_ne_zero had, Nat.pos_of_ne_zero hbd⟩

lemma HasBinaryEndpoints.monic_factors_of_reducible {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hn : 1 ≤ n) (hred : ReducibleOverRat p) :
    ∃ a b : ℤ[X], a.Monic ∧ b.Monic ∧ p = a * b ∧
      0 < a.natDegree ∧ 0 < b.natDegree :=
  monic_factors_of_reducibleOverRat hp.monic (by rw [hp.degree]; omega) hred

end OdlyzkoPoonen
