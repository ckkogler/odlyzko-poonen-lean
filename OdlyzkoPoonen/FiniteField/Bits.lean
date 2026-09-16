import OdlyzkoPoonen.Polynomial.BinaryWords
import Mathlib.Data.ZMod.Basic

/-!
# Boolean coordinates for the field with two elements

The explicit equivalence sends false to zero and true to one. Xor corresponds
to field addition, and complementation corresponds to adding one. These facts
connect finite fair-bit counting to polynomial discrepancy coefficients.
-/

namespace OdlyzkoPoonen

/-- The usual field value of a bit. -/
def bitToF2 (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The Boolean value of a coefficient in the field with two elements. -/
def f2ToBit (c : ZMod 2) : Bool := decide (c = 1)

lemma bitToF2_eq_int_cast (b : Bool) : bitToF2 b = (bitValue b : ZMod 2) := by
  cases b <;> rfl

lemma f2ToBit_bitToF2 (b : Bool) : f2ToBit (bitToF2 b) = b := by
  cases b <;> rfl

lemma bitToF2_f2ToBit (c : ZMod 2) : bitToF2 (f2ToBit c) = c := by
  fin_cases c <;> rfl

/-- The explicit false/zero, true/one equivalence. -/
def bitF2Equiv : Bool ≃ ZMod 2 where
  toFun := bitToF2
  invFun := f2ToBit
  left_inv := f2ToBit_bitToF2
  right_inv := bitToF2_f2ToBit

lemma bitToF2_xor (b c : Bool) :
    bitToF2 (Bool.xor b c) = bitToF2 b + bitToF2 c := by
  cases b <;> cases c <;> rfl

lemma bitToF2_not (b : Bool) : bitToF2 (!b) = bitToF2 b + 1 := by
  cases b <;> rfl

lemma f2ToBit_add_one (c : ZMod 2) : f2ToBit (c + 1) = !(f2ToBit c) := by
  fin_cases c <;> rfl

lemma f2ToBit_eq_false_iff (c : ZMod 2) : f2ToBit c = false ↔ c = 0 := by
  fin_cases c
  · change (false = false ↔ (0 : ZMod 2) = 0)
    simp
  · change (true = false ↔ (1 : ZMod 2) = 0)
    simp

lemma f2ToBit_eq_true_iff (c : ZMod 2) : f2ToBit c = true ↔ c = 1 := by
  simp [f2ToBit]

end OdlyzkoPoonen
