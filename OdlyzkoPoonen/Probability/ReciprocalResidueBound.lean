import OdlyzkoPoonen.Probability.ReciprocalSumDivisors
import OdlyzkoPoonen.Arithmetic.OppositeResiduePairs
import OdlyzkoPoonen.Analysis.ResidueExponentialBound

/-!
# Exponential probability for a determining divisor at a fixed prime

The integer reciprocal sum may select its irreducible divisor after the word
is observed. Conditioning and averaging over opposite pairs still yield a
uniform estimate, without requiring the sampled polynomial to be noncyclotomic.
-/

namespace OdlyzkoPoonen

lemma binaryProbability_reciprocalSumDivisor_le_exp {n q : ℕ} {B : ℝ}
    (hq : q.Prime) (hq3 : 3 ≤ q) (hn : 4 * q ≤ n) (hB : (q : ℝ) ≤ B) :
    binaryProbability (n - 1) (HasSeparatedReciprocalSumDivisor (n - 1) q) ≤
      n * Real.exp (-(n : ℝ) / (16 * B)) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨a, ha, hdouble⟩ := exists_half_residue (hq.odd_of_ne_two (by omega)) n
  have hdouble' : (2 * a) % q = (n - 1 + 1) % q := by
    rwa [Nat.sub_add_cancel hn1]
  let s := oppositeResiduePairs (n - 1) q a
  calc
    _ ≤ (((n - 1 : ℕ) : ℝ) + 1) * (3 / 4 : ℝ) ^ s.card :=
      binaryProbability_reciprocalSumDivisor_le hq.pos ha s
        (oppositeResiduePairs_positions ha hdouble')
    _ = (n : ℝ) * (3 / 4 : ℝ) ^ s.card := by
      congr 1
      exact_mod_cast Nat.sub_add_cancel hn1
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (three_quarters_pow_le_exp hq.pos hB (oppositeResiduePairs_card_ge_degree hq.pos ha hn))
      (Nat.cast_nonneg n)

end OdlyzkoPoonen
