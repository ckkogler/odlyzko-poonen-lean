import OdlyzkoPoonen.Polynomial.Reversal
import Mathlib.Data.ZMod.Basic

/-!
# Coefficient reduction and the zero-one lift

Reduction is the ordinary polynomial map induced by integer reduction. In the
opposite direction, `zeroOneLift` chooses the representatives zero and one of
each coefficient over `ZMod 2`. This lift is a map of sets, not a ring map:
products are taken over the finite field before lifting.
-/

namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators

/-- Ordinary coefficientwise reduction modulo `r`. -/
noncomputable def reducePolynomial (r : ℕ) (p : ℤ[X]) : (ZMod r)[X] :=
  p.map (Int.castRingHom (ZMod r))

lemma coeff_reducePolynomial (r : ℕ) (p : ℤ[X]) (k : ℕ) :
    (reducePolynomial r p).coeff k = (p.coeff k : ZMod r) := by
  simp [reducePolynomial]

lemma reducePolynomial_mul (r : ℕ) (p q : ℤ[X]) :
    reducePolynomial r (p * q) = reducePolynomial r p * reducePolynomial r q := by
  simp [reducePolynomial]

/-- The coefficientwise zero-one representative of a polynomial over `ZMod 2`. -/
noncomputable def zeroOneLift (p : (ZMod 2)[X]) : ℤ[X] :=
  p.sum (fun k c ↦ monomial k (c.val : ℤ))

lemma coeff_zeroOneLift (p : (ZMod 2)[X]) (k : ℕ) :
    (zeroOneLift p).coeff k = ((p.coeff k).val : ℤ) := by
  classical
  simp only [zeroOneLift, sum_def, finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hk : k ∈ p.support
  · simp only [Finset.sum_ite_eq', ite_eq_left hk]
  · have hc : p.coeff k = 0 := notMem_support_iff.mp hk
    simp only [Finset.sum_ite_eq', ite_eq_right hk, hc, ZMod.val_zero, Nat.cast_zero]

lemma zeroOneLift_binary (p : (ZMod 2)[X]) : IsBinary (zeroOneLift p) := by
  intro k
  rw [coeff_zeroOneLift]
  have h := (p.coeff k).val_lt
  have : (p.coeff k).val = 0 ∨ (p.coeff k).val = 1 := by omega
  rcases this with h | h <;> simp [h]

lemma reduce_zeroOneLift (p : (ZMod 2)[X]) :
    reducePolynomial 2 (zeroOneLift p) = p := by
  ext k
  simp [coeff_reducePolynomial, coeff_zeroOneLift]

lemma zeroOneLift_reduce {p : ℤ[X]} (hp : IsBinary p) :
    zeroOneLift (reducePolynomial 2 p) = p := by
  ext k
  rw [coeff_zeroOneLift, coeff_reducePolynomial]
  rcases hp k with h | h <;>
    simp only [h, Int.cast_zero, Int.cast_one, ZMod.val_zero, ZMod.val_one,
      Nat.cast_zero, Nat.cast_one]

lemma zeroOneLift_injective : Function.Injective zeroOneLift := by
  intro p q h
  simpa only [reduce_zeroOneLift] using congrArg (reducePolynomial 2) h

lemma IsBinary.eq_of_reduce_eq {p q : ℤ[X]} (hp : IsBinary p) (hq : IsBinary q)
    (h : reducePolynomial 2 p = reducePolynomial 2 q) : p = q := by
  simpa only [zeroOneLift_reduce hp, zeroOneLift_reduce hq] using congrArg zeroOneLift h

lemma support_zeroOneLift (p : (ZMod 2)[X]) :
    (zeroOneLift p).support = p.support := by
  ext k
  simp only [mem_support_iff, coeff_zeroOneLift]
  constructor
  · intro h hc
    apply h
    rw [hc]
    rfl
  · intro h hc
    apply h
    apply (ZMod.val_eq_zero _).mp
    exact_mod_cast hc

lemma natDegree_zeroOneLift (p : (ZMod 2)[X]) :
    (zeroOneLift p).natDegree = p.natDegree := by
  apply le_antisymm <;> apply natDegree_le_natDegree <;> apply degree_mono
  · rw [support_zeroOneLift]
  · rw [support_zeroOneLift]

lemma zeroOneLift_reverse (p : (ZMod 2)[X]) :
    zeroOneLift p.reverse = (zeroOneLift p).reverse := by
  ext k
  simp only [coeff_zeroOneLift, coeff_reverse, natDegree_zeroOneLift]

lemma IsBinary.natDegree_reduce {p : ℤ[X]} (hp : IsBinary p) :
    (reducePolynomial 2 p).natDegree = p.natDegree := by
  rw [← natDegree_zeroOneLift, zeroOneLift_reduce hp]

lemma IsBinary.reduce_reverse {p : ℤ[X]} (hp : IsBinary p) :
    reducePolynomial 2 p.reverse = (reducePolynomial 2 p).reverse := by
  ext k
  simp only [coeff_reducePolynomial, coeff_reverse, hp.natDegree_reduce]

/-- Coefficientwise congruence, using the ordinary reduction ring map. -/
def CongruentMod (r : ℕ) (p q : ℤ[X]) : Prop :=
  reducePolynomial r p = reducePolynomial r q

lemma congruentMod_iff_coeff_dvd (r : ℕ) (p q : ℤ[X]) :
    CongruentMod r p q ↔ ∀ k, (r : ℤ) ∣ p.coeff k - q.coeff k := by
  unfold CongruentMod
  rw [Polynomial.ext_iff]
  simp only [coeff_reducePolynomial]
  constructor
  · intro h k
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ r).mp (h k).symm
  · intro h k
    exact ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ r).mpr (h k)).symm

end OdlyzkoPoonen
