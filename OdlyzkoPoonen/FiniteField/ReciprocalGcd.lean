import OdlyzkoPoonen.FiniteField.GcdFactors

/-!
# The reciprocal gcd of an endpoint polynomial

The actual monic gcd of a polynomial and its reverse has constant coefficient
one. Reversing the two divisibilities shows that its reverse divides the gcd
itself. Their degrees agree, so monicity makes them equal. These algebraic facts
supply the reciprocal divisor in the finite-field tail estimate.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma f2_reverse_dvd_reverse {a b : (ZMod 2)[X]} (hab : a ∣ b) :
    a.reverse ∣ b.reverse := by
  obtain ⟨q, rfl⟩ := hab
  rw [reverse_mul_of_domain]
  exact dvd_mul_right _ _

lemma HasF2Endpoints.divisor_endpoints {n : ℕ} {p a : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) (ha : a ∣ p) : HasF2Endpoints a.natDegree a := by
  obtain ⟨b, hb⟩ := ha
  exact (hp.factor_endpoints hb).1

lemma HasF2Endpoints.gcd_reverse_endpoints {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) :
    HasF2Endpoints (GCDMonoid.gcd p p.reverse).natDegree (GCDMonoid.gcd p p.reverse) :=
  hp.divisor_endpoints (gcd_dvd_left p p.reverse)

lemma HasF2Endpoints.gcd_reverse_degree_le {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) : (GCDMonoid.gcd p p.reverse).natDegree ≤ n := by
  simpa only [hp.degree] using
    natDegree_le_of_dvd (gcd_dvd_left p p.reverse) hp.monic.ne_zero

lemma HasF2Endpoints.gcd_reverse_reciprocal {n : ℕ} {p : (ZMod 2)[X]}
    (hp : HasF2Endpoints n p) :
    (GCDMonoid.gcd p p.reverse).reverse = GCDMonoid.gcd p p.reverse := by
  let g := GCDMonoid.gcd p p.reverse
  have hg : HasF2Endpoints g.natDegree g := hp.gcd_reverse_endpoints
  have hgp : g.reverse ∣ p := by
    have h := f2_reverse_dvd_reverse (gcd_dvd_right p p.reverse)
    simpa only [hp.reverse_reverse] using h
  have hgr : g.reverse ∣ p.reverse :=
    f2_reverse_dvd_reverse (gcd_dvd_left p p.reverse)
  have hdvd : g.reverse ∣ g := dvd_gcd hgp hgr
  exact (eq_of_monic_of_dvd_of_natDegree_le hg.reverse.monic hg.monic hdvd
    (by rw [hg.reverse.degree])).symm

end OdlyzkoPoonen
