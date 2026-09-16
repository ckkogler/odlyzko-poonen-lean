import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# Products of primitive roots with coprime orders

The coprime-order formula for a product is used when two Galois-conjugate
root ratios are arranged to have the same numerator.
-/

namespace OdlyzkoPoonen

lemma primitiveRoot_mul_of_coprime {M : Type*} [CommMonoid M]
    {x y : M} {r s : ℕ} (hx : IsPrimitiveRoot x r) (hy : IsPrimitiveRoot y s)
    (hrs : r.Coprime s) : IsPrimitiveRoot (x * y) (r * s) := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  have hc : (orderOf x).Coprime (orderOf y) := by
    rwa [← hx.eq_orderOf, ← hy.eq_orderOf]
  rw [(Commute.all x y).orderOf_mul_eq_mul_orderOf_of_coprime hc,
    ← hx.eq_orderOf, ← hy.eq_orderOf]

end OdlyzkoPoonen
