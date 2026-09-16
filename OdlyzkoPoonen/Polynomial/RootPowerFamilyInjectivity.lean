import OdlyzkoPoonen.Polynomial.RootPowerFamilies

/-!
# Joint injectivity of powered root families

Separation within each exponent and noncollision across distinct exponents
make the group/root pair map injective. Inserting exponent one before a family
of distinct primes preserves injectivity of the exponent labels.
-/

namespace OdlyzkoPoonen
open Polynomial

lemma option_prime_exponents_injective {ι : Type*} (p : ι → ℕ)
    (hpinj : Function.Injective p) (hp : ∀ i, (p i).Prime) :
    Function.Injective (fun t : Option ι ↦ t.elim 1 p) := by
  intro t u he
  cases t with
  | none =>
    cases u with
    | none => rfl
    | some i => exact False.elim ((hp i).ne_one he.symm)
  | some i =>
    cases u with
    | none => exact False.elim ((hp i).ne_one he)
    | some j => exact congrArg some (hpinj he)

lemma root_power_pair_injective {ι β : Type*} {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J) (r : ι → ℕ) (hr : Function.Injective r)
    (α : β → ℂ) (hα : Function.Injective α)
    (hmem : ∀ a, α a ∈ (J.map (Int.castRingHom ℂ)).roots)
    (hsep : ∀ t, ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ r t = b ^ r t → a = b) :
    Function.Injective (fun z : ι × β ↦ α z.2 ^ r z.1) := by
  rintro ⟨t, a⟩ ⟨u, b⟩ he
  have htu : t = u := hr (eq_exponents_of_noncyclotomic_complex_root_powers
    hJ hirr hconst hcyc (hmem a) (hmem b) he)
  subst u
  have hab : a = b := hα (hsep t _ (hmem a) _ (hmem b) he)
  subst b
  rfl

end OdlyzkoPoonen
