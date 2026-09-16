import OdlyzkoPoonen.Polynomial.Reduction

/-!
# Reduction of monic polynomials preserves degree and reversal

The coefficients of a monic polynomial need not be binary. Its leading one
survives any reduction into a nontrivial ring, so the degree is unchanged and
the degree-based ordinary reversal commutes with reduction.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma monic_reduce_natDegree (r : ℕ) [Nontrivial (ZMod r)] {p : ℤ[X]} (hp : p.Monic) :
    (reducePolynomial r p).natDegree = p.natDegree :=
  hp.natDegree_map (Int.castRingHom (ZMod r))

lemma monic_reduce_reverse (r : ℕ) [Nontrivial (ZMod r)] {p : ℤ[X]} (hp : p.Monic) :
    reducePolynomial r p.reverse = (reducePolynomial r p).reverse := by
  ext k
  simp only [coeff_reducePolynomial, coeff_reverse, monic_reduce_natDegree r hp]

lemma reducePolynomial_dvd (r : ℕ) {a b : ℤ[X]} (hab : a ∣ b) :
    reducePolynomial r a ∣ reducePolynomial r b := by
  obtain ⟨q, hq⟩ := hab
  exact ⟨reducePolynomial r q, by rw [hq, reducePolynomial_mul]⟩

end OdlyzkoPoonen
