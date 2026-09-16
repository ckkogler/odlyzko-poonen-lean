import OdlyzkoPoonen.FiniteField.Bits

/-! # Zero and one tests for Boolean coefficients -/

namespace OdlyzkoPoonen

lemma bitToF2_eq_zero_iff (b : Bool) : bitToF2 b = 0 ↔ b = false := by
  cases b <;> simp [bitToF2]

lemma bitToF2_eq_one_iff (b : Bool) : bitToF2 b = 1 ↔ b = true := by
  cases b <;> simp [bitToF2]

end OdlyzkoPoonen
