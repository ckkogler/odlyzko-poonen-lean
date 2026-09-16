import OdlyzkoPoonen.Polynomial.Reduction
import OdlyzkoPoonen.Polynomial.BinaryWords

/-!
# Endpoint families over the field with two elements

`HasF2Endpoints n` is precisely the monic degree-`n` family with constant one.
There is no additional coefficient restriction over `ZMod 2`. Reduction and
zero-one lifting identify this family with the integer binary family, including
its exact cardinality. The parameter `m` in finite enumerations counts internal
bits, so their polynomial degree is `m + 1`.
-/

namespace OdlyzkoPoonen
open Polynomial

/-- A monic polynomial over the field with two elements, with fixed degree and
constant coefficient one. -/
structure HasF2Endpoints (n : ℕ) (p : (ZMod 2)[X]) : Prop where
  monic : p.Monic
  degree : p.natDegree = n
  constant : p.coeff 0 = 1

lemma HasBinaryEndpoints.reduce {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) : HasF2Endpoints n (reducePolynomial 2 p) := by
  refine ⟨hp.monic.map _, hp.binary.natDegree_reduce.trans hp.degree, ?_⟩
  rw [coeff_reducePolynomial, hp.constant]
  norm_num

lemma HasF2Endpoints.lift {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) : HasBinaryEndpoints n (zeroOneLift p) := by
  refine ⟨?_, (natDegree_zeroOneLift p).trans hp.degree, ?_, zeroOneLift_binary p⟩
  · change (zeroOneLift p).coeff (zeroOneLift p).natDegree = 1
    rw [natDegree_zeroOneLift, coeff_zeroOneLift]
    have hc : p.coeff p.natDegree = 1 := hp.monic
    rw [hc]
    norm_num [ZMod.val_one]
  · rw [coeff_zeroOneLift, hp.constant]
    norm_num [ZMod.val_one]

lemma zeroOneLift_endpoints_iff {n : ℕ} {p : (ZMod 2)[X]} :
    HasBinaryEndpoints n (zeroOneLift p) ↔ HasF2Endpoints n p := by
  constructor
  · intro hp
    simpa only [reduce_zeroOneLift] using hp.reduce
  · exact HasF2Endpoints.lift

lemma HasF2Endpoints.reverse {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) : HasF2Endpoints n p.reverse := by
  apply zeroOneLift_endpoints_iff.mp
  rw [zeroOneLift_reverse]
  exact hp.lift.reverse

lemma HasF2Endpoints.mul {d e : ℕ} {a b : (ZMod 2)[X]}
    (ha : HasF2Endpoints d a) (hb : HasF2Endpoints e b) :
    HasF2Endpoints (d + e) (a * b) := by
  refine ⟨ha.monic.mul hb.monic, ?_, ?_⟩
  · rw [natDegree_mul ha.monic.ne_zero hb.monic.ne_zero, ha.degree, hb.degree]
  · rw [mul_coeff_zero, ha.constant, hb.constant, one_mul]

/-- Reduction of the binary word polynomial to the field with two elements. -/
noncomputable def f2WordPolynomial {m : ℕ} (w : Fin m → Bool) : (ZMod 2)[X] :=
  reducePolynomial 2 (wordPolynomial w)

lemma f2WordPolynomial_endpoints {m : ℕ} (w : Fin m → Bool) :
    HasF2Endpoints (m + 1) (f2WordPolynomial w) :=
  (wordPolynomial_endpoints w).reduce

lemma f2WordPolynomial_injective {m : ℕ} :
    Function.Injective (@f2WordPolynomial m) := by
  intro v w h
  apply wordPolynomial_injective
  exact (wordPolynomial_endpoints v).binary.eq_of_reduce_eq
    (wordPolynomial_endpoints w).binary h

lemma exists_f2WordPolynomial_eq {m : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints (m + 1) p) :
    ∃ w : Fin m → Bool, f2WordPolynomial w = p := by
  obtain ⟨w, hw⟩ := exists_wordPolynomial_eq hp.lift
  refine ⟨w, ?_⟩
  unfold f2WordPolynomial
  rw [hw, reduce_zeroOneLift]

/-- The finite field endpoint family, with `m` intermediate coefficients. -/
noncomputable def f2Family (m : ℕ) : Finset (ZMod 2)[X] :=
  Finset.univ.image (@f2WordPolynomial m)

lemma mem_f2Family_iff {m : ℕ} {p : (ZMod 2)[X]} :
    p ∈ f2Family m ↔ HasF2Endpoints (m + 1) p := by
  classical
  constructor
  · intro h
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp h
    exact f2WordPolynomial_endpoints w
  · intro hp
    obtain ⟨w, rfl⟩ := exists_f2WordPolynomial_eq hp
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩

lemma card_f2Family (m : ℕ) : (f2Family m).card = 2 ^ m := by
  classical
  rw [f2Family, Finset.card_image_of_injective _ f2WordPolynomial_injective]
  simp

end OdlyzkoPoonen
