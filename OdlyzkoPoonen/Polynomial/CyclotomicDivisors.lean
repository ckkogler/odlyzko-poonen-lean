import OdlyzkoPoonen.Polynomial.PositiveRealRoots
import OdlyzkoPoonen.Polynomial.RationalReducibility
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Cyclotomic divisors and the two degree-one cases

A cyclotomic divisor has positive order: the convention `cyclotomic 0 = 1`
must not make the event automatic. The higher-degree event uses precisely
`totient k ≥ 2`. For an endpoint-one binary polynomial the order-one divisor
is impossible, and the order-two divisor is equivalent to a root at minus one.
-/

namespace OdlyzkoPoonen
open Polynomial

/-- Divisibility by an actual cyclotomic polynomial of positive order. -/
def HasCyclotomicDivisor (p : ℤ[X]) : Prop :=
  ∃ k : ℕ, 0 < k ∧ cyclotomic k ℤ ∣ p

/-- The source's event of a cyclotomic divisor of degree at least two. -/
def HasHigherCyclotomicDivisor (p : ℤ[X]) : Prop :=
  ∃ k : ℕ, 2 ≤ k.totient ∧ cyclotomic k ℤ ∣ p

lemma HasCyclotomicDivisor.of_dvd {p q : ℤ[X]} (hp : HasCyclotomicDivisor p)
    (hdvd : p ∣ q) : HasCyclotomicDivisor q := by
  obtain ⟨k, hk, hkp⟩ := hp
  exact ⟨k, hk, hkp.trans hdvd⟩

lemma HasHigherCyclotomicDivisor.hasCyclotomicDivisor {p : ℤ[X]}
    (hp : HasHigherCyclotomicDivisor p) : HasCyclotomicDivisor p := by
  obtain ⟨k, hk, hd⟩ := hp
  exact ⟨k, Nat.totient_pos.mp (by omega), hd⟩

lemma cyclotomic_dvd_iff_rational (k : ℕ) (p : ℤ[X]) :
    cyclotomic k ℤ ∣ p ↔ cyclotomic k ℚ ∣ p.map (Int.castRingHom ℚ) := by
  rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ (cyclotomic.isPrimitive k ℤ),
    map_cyclotomic_int]

lemma HasBinaryEndpoints.eval_int_one_pos {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : 0 < p.eval 1 := by
  have h := hp.eval_real_pos (t := 1) (by norm_num)
  rw [eval₂_at_one] at h
  change (0 : ℝ) < ((p.eval 1 : ℤ) : ℝ) at h
  exact_mod_cast h

lemma HasBinaryEndpoints.not_cyclotomic_one_dvd {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : ¬ cyclotomic 1 ℤ ∣ p := by
  intro hd
  have hz : IsRoot p (1 : ℤ) := by
    apply dvd_iff_isRoot.mp
    simpa only [cyclotomic_one, C_1] using hd
  have hpos := hp.eval_int_one_pos
  change p.eval 1 = 0 at hz
  omega

lemma cyclotomic_two_dvd_iff_minus_one (p : ℤ[X]) :
    cyclotomic 2 ℤ ∣ p ↔ p.eval (-1) = 0 := by
  simpa [cyclotomic_two, IsRoot.def] using (dvd_iff_isRoot (p := p) (a := (-1 : ℤ)))

lemma HasBinaryEndpoints.cyclotomic_alternative {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hcyc : HasCyclotomicDivisor p) :
    HasHigherCyclotomicDivisor p ∨ p.eval (-1) = 0 := by
  obtain ⟨k, hk, hd⟩ := hcyc
  by_cases hhigh : 2 ≤ k.totient
  · exact Or.inl ⟨k, hhigh, hd⟩
  have ht : k.totient = 1 := by have := Nat.totient_pos.mpr hk; omega
  rcases Nat.totient_eq_one_iff.mp ht with rfl | rfl
  · exact False.elim (hp.not_cyclotomic_one_dvd hd)
  · exact Or.inr ((cyclotomic_two_dvd_iff_minus_one p).mp hd)

lemma HasBinaryEndpoints.hasCyclotomicDivisor_iff {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) :
    HasCyclotomicDivisor p ↔ HasHigherCyclotomicDivisor p ∨ p.eval (-1) = 0 := by
  refine ⟨hp.cyclotomic_alternative, ?_⟩
  rintro (h | h)
  · exact h.hasCyclotomicDivisor
  · exact ⟨2, by norm_num, (cyclotomic_two_dvd_iff_minus_one p).mpr h⟩

end OdlyzkoPoonen
