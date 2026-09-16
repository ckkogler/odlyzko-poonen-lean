import OdlyzkoPoonen.LinearAlgebra.RootPowerDeterminantUpperBound
import OdlyzkoPoonen.LinearAlgebra.RootPowerDeterminantLowerBound

/-!
# A quantitative Mahler inequality from finite prime families

The actual root family and determinant enumeration are constructed internally.
Combining the integer lower bound with the Mahler upper bound leaves only the
finite family of distinct separating primes as an arithmetic input.
-/

noncomputable section
namespace OdlyzkoPoonen
open Polynomial
open scoped BigOperators Classical

lemma prime_family_mahler_power_inequality {ι : Type*} [Fintype ι]
    {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J)
    (p : ι → ℕ) (hpinj : Function.Injective p) (hp : ∀ i, (p i).Prime)
    (hsep : ∀ i, ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ p i = b ^ p i → a = b)
    {k : ℕ} (hk : 0 < k) :
    (∏ i, (p i : ℝ)) ^ (2 * J.natDegree * k) ≤
      (((J.natDegree * (k + Fintype.card ι) : ℕ) : ℝ) ^
          (J.natDegree * (k ^ 2 + k + 2 * Fintype.card ι)) *
        (J.map (Int.castRingHom ℂ)).mahlerMeasure ^
          (J.natDegree * (k + Fintype.card ι) * (k + ∑ i, p i))) ^ 2 := by
  obtain ⟨α, hα, hmem, hfac⟩ := exists_integer_root_family hJ hirr
  let n := J.natDegree * (k + Fintype.card ι)
  have hd : 0 < J.natDegree := by
    have h := hirr.natDegree_pos
    rwa [hJ.natDegree_map] at h
  have hn : 1 ≤ n := Nat.mul_pos hd (Nat.add_pos_left hk _)
  have hc : Fintype.card (Σ t : Option ι,
      Fin (t.elim k (fun _ ↦ 1)) × Fin J.natDegree) = n := by
    simpa only [Fintype.card_fin] using card_repeated_option_family (β := Fin J.natDegree) k
  let e : Fin n ≃ (Σ t : Option ι, Fin (t.elim k (fun _ ↦ 1)) × Fin J.natDegree) :=
    (Fintype.equivFinOfCardEq hc).symm
  have hl := root_power_determinant_lower_bound hJ hirr hconst hcyc p hpinj hp
    α hα hmem hfac hsep k e
  have hu := root_power_determinant_upper_bound hJ hirr hconst hcyc p hpinj hp
    α hα hmem hfac hsep k hn e
  exact hl.trans (pow_le_pow_left₀ (norm_nonneg _) hu 2)

lemma prime_family_mahler_log_inequality {ι : Type*} [Fintype ι]
    {J : ℤ[X]} (hJ : J.Monic)
    (hirr : Irreducible (J.map (Int.castRingHom ℚ))) (hconst : J.coeff 0 ≠ 0)
    (hcyc : ¬ HasCyclotomicDivisor J)
    (p : ι → ℕ) (hpinj : Function.Injective p) (hp : ∀ i, (p i).Prime)
    (hsep : ∀ i, ∀ a ∈ (J.map (Int.castRingHom ℂ)).roots,
      ∀ b ∈ (J.map (Int.castRingHom ℂ)).roots, a ^ p i = b ^ p i → a = b)
    {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * (∑ i, Real.log (p i : ℝ)) ≤
      ((k : ℝ) ^ 2 + k + 2 * (Fintype.card ι : ℝ)) *
          Real.log ((J.natDegree : ℝ) * (k + (Fintype.card ι : ℝ))) +
        ((k : ℝ) + Fintype.card ι) * (k + ∑ i, (p i : ℝ)) *
          Real.log (J.map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hd : 0 < (J.natDegree : ℝ) := by
    have h := hirr.natDegree_pos
    rw [hJ.natDegree_map] at h
    exact_mod_cast h
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hprod : 0 < ∏ i, (p i : ℝ) :=
    Finset.prod_pos (fun i _ ↦ by exact_mod_cast (hp i).pos)
  have hM : 0 < (J.map (Int.castRingHom ℂ)).mahlerMeasure :=
    mahlerMeasure_pos_of_ne_zero (hJ.map _).ne_zero
  have hN : 0 < (J.natDegree : ℝ) * (k + (Fintype.card ι : ℝ)) := by positivity
  have hNcast : (0 : ℝ) < ((J.natDegree * (k + Fintype.card ι) : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using hN
  have hbound := prime_family_mahler_power_inequality hJ hirr hconst hcyc p hpinj hp hsep hk
  have hlog := Real.log_le_log (pow_pos hprod _) hbound
  simp only [Real.log_pow] at hlog
  rw [Real.log_mul (pow_ne_zero _ hNcast.ne') (pow_ne_zero _ hM.ne'), Real.log_pow, Real.log_pow] at hlog
  rw [Real.log_prod (fun i _ ↦ by exact_mod_cast (hp i).ne_zero)] at hlog
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_sum] at hlog
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * (J.natDegree : ℝ) by positivity)).mp
  convert! hlog using 1 <;> ring

end OdlyzkoPoonen
