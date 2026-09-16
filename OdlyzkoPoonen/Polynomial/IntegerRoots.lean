import OdlyzkoPoonen.Polynomial.RationalReducibility

/-!
# Integer roots force rational reducibility in degree at least two

The ordinary coefficient map preserves integer evaluations and the degree of a
monic polynomial. An irreducible polynomial with a root over the base field has
degree one, so it cannot have one of these roots in degree at least two.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma monic_reducibleOverRat_of_integer_root {p : ℤ[X]} (hp : p.Monic)
    (hdegree : 2 ≤ p.natDegree) {t : ℤ} (hroot : p.eval t = 0) :
    ReducibleOverRat p := by
  intro hi
  have hr : IsRoot (p.map (Int.castRingHom ℚ)) ((Int.castRingHom ℚ) t) := by
    change (p.map (Int.castRingHom ℚ)).eval ((Int.castRingHom ℚ) t) = 0
    rw [eval_map_apply, hroot, map_zero]
  have hd := natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root hi hr)
  rw [hp.natDegree_map] at hd
  change p.natDegree = 1 at hd
  omega

lemma HasBinaryEndpoints.reducible_of_minus_one {n : ℕ} {p : ℤ[X]}
    (hp : HasBinaryEndpoints n p) (hn : 2 ≤ n) (hroot : p.eval (-1) = 0) :
    ReducibleOverRat p :=
  monic_reducibleOverRat_of_integer_root hp.monic (by rwa [hp.degree]) hroot

end OdlyzkoPoonen
