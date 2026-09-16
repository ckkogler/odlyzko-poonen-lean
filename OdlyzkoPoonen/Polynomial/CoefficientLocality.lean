import OdlyzkoPoonen.Polynomial.OuterAutocorrelation

/-!
# Locality of polynomial coefficients

A product coefficient uses only coefficients through that index. An outer
autocorrelation coefficient uses the same number of coefficients at both ends.
`AgreeOnOuter` records these actual coefficient equalities, without encoding
any probability or congruence conclusion.
-/

namespace OdlyzkoPoonen
open Polynomial

/-- Agreement through `k` at both ends of the degree window `n`. -/
def AgreeOnOuter {R : Type*} [Semiring R] (n k : ℕ) (p q : R[X]) : Prop :=
  (∀ i ≤ k, p.coeff i = q.coeff i) ∧
  (∀ i ≤ k, p.coeff (n - i) = q.coeff (n - i))

lemma AgreeOnOuter.mono {R : Type*} [Semiring R] {n k l : ℕ} {p q : R[X]}
    (h : AgreeOnOuter n k p q) (hl : l ≤ k) : AgreeOnOuter n l p q :=
  ⟨fun i hi ↦ h.1 i (hi.trans hl), fun i hi ↦ h.2 i (hi.trans hl)⟩

lemma coeff_mul_right_eq_of_prefix {R : Type*} [Semiring R] (a : R[X])
    {b b' : R[X]} {k : ℕ} (h : ∀ i ≤ k, b.coeff i = b'.coeff i) :
    (a * b).coeff k = (a * b').coeff k := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [h ij.2 (by have := Finset.mem_antidiagonal.mp hij; omega)]

lemma AgreeOnOuter.autocorrelation {n k : ℕ} {p q : ℤ[X]}
    (h : AgreeOnOuter n k p q) (hp : p.natDegree = n) (hq : q.natDegree = n)
    (hk : k ≤ n) : (autocorrelation p).coeff k = (autocorrelation q).coeff k := by
  rw [coeff_autocorrelation_le p (by rw [hp]; exact hk),
    coeff_autocorrelation_le q (by rw [hq]; exact hk), hp, hq]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [h.1 i hik, show n - k + i = n - (k - i) by omega, h.2 (k - i) (by omega)]

end OdlyzkoPoonen
