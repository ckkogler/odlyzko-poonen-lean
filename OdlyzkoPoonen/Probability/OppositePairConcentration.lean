import OdlyzkoPoonen.Probability.SelectedBitWeights
import OdlyzkoPoonen.Probability.FiniteSetUnion
import OdlyzkoPoonen.Arithmetic.OppositeResiduePairs
import OdlyzkoPoonen.Analysis.ResidueExponentialBound

/-!
# Concentration of unequal opposite pairs over a prime interval

At scale `T`, the eligible positions for each prime at most `2T` number at
least `n/(8T)`. Their independent fair mask bits give the explicit exceptional
probability `2T*exp(-n/(128T))` for any prime to have fewer than `n/(32T)`
unequal pairs. The prime interval and all events below are actual finite sets.
-/

namespace OdlyzkoPoonen
open scoped Classical

lemma uniformProbability_selected_count_lt_le_exp {ι : Type*} [Fintype ι]
    (s : Finset ι) {n T : ℝ} (_hT : 0 < T) (hcard : n / (8 * T) ≤ s.card) :
    uniformProbability (fun c : ι → Bool ↦ (selectedTrueCount s c : ℝ) < n / (32 * T)) ≤
      Real.exp (-n / (128 * T)) := by
  have hmono : uniformProbability (fun c : ι → Bool ↦ (selectedTrueCount s c : ℝ) < n / (32 * T)) ≤
      uniformProbability (fun c : ι → Bool ↦ 4 * selectedTrueCount s c ≤ s.card) := by
    apply uniformProbability_mono
    intro c hc
    have h : (4 : ℝ) * selectedTrueCount s c ≤ s.card := by
      calc
        _ ≤ 4 * (n / (32 * T)) := mul_le_mul_of_nonneg_left hc.le (by norm_num)
        _ = n / (8 * T) := by ring
        _ ≤ _ := hcard
    exact_mod_cast h
  have hrate : n / (128 * T) ≤ (s.card : ℝ) / 16 := by
    calc
      _ = (n / (8 * T)) / 16 := by rw [div_div]; congr 1; ring
      _ ≤ _ := div_le_div_of_nonneg_right hcard (by norm_num)
  refine (hmono.trans (uniformProbability_selectedTrueCount_lower_tail_exp s)).trans ?_
  exact Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hrate)

noncomputable def concentrationPrimes (T : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊2 * T⌋₊).filter (fun q ↦ q.Prime ∧ T < (q : ℝ))

noncomputable def primeOppositePairs (n q : ℕ) : Finset (Fin ((n - 1) / 2)) :=
  oppositeResiduePairs (n - 1) q ((n * ((q + 1) / 2)) % q)

def HasSparseOppositePrimePairs (n : ℕ) (T : ℝ) (c : Fin ((n - 1) / 2) → Bool) : Prop :=
  ∃ q ∈ concentrationPrimes T,
    (selectedTrueCount (primeOppositePairs n q) c : ℝ) < (n : ℝ) / (32 * T)

lemma concentrationPrimes_card_le {T : ℝ} (hT : 0 ≤ T) :
    ((concentrationPrimes T).card : ℝ) ≤ 2 * T := by
  have h : (concentrationPrimes T).card ≤ ⌊2 * T⌋₊ := by
    have hh := Finset.card_filter_le (Finset.Icc 1 ⌊2 * T⌋₊) (fun q ↦ q.Prime ∧ T < (q : ℝ))
    simpa only [concentrationPrimes, Nat.card_Icc, Nat.add_sub_cancel] using hh
  exact (by exact_mod_cast h : ((concentrationPrimes T).card : ℝ) ≤ ⌊2 * T⌋₊).trans
    (Nat.floor_le (by positivity))

lemma primeOppositePairs_card_ge {n q : ℕ} {T : ℝ}
    (hT : 2 ≤ T) (hn : 8 * T ≤ (n : ℝ)) (hq : q ∈ concentrationPrimes T) :
    (n : ℝ) / (8 * T) ≤ (primeOppositePairs n q).card := by
  obtain ⟨hqinterval, hp, _⟩ := Finset.mem_filter.mp hq
  have hqhi : (q : ℝ) ≤ 2 * T :=
    (by exact_mod_cast (Finset.mem_Icc.mp hqinterval).2 : (q : ℝ) ≤ ⌊2 * T⌋₊).trans
      (Nat.floor_le (by positivity))
  have hqn : 4 * q ≤ n := by
    have h : (4 : ℝ) * q ≤ n := by linarith
    exact_mod_cast h
  have hqR : (0 : ℝ) < q := by exact_mod_cast hp.pos
  calc
    _ ≤ (n : ℝ) / (4 * q) := div_le_div_of_nonneg_left (Nat.cast_nonneg n)
      (by positivity) (by linarith)
    _ ≤ _ := oppositeResiduePairs_card_ge_degree hp.pos (Nat.mod_lt _ hp.pos) hqn

theorem opposite_prime_pairs_concentration {n : ℕ} {T : ℝ}
    (hT : 2 ≤ T) (hn : 8 * T ≤ (n : ℝ)) :
    uniformProbability (HasSparseOppositePrimePairs n T) ≤
      2 * T * Real.exp (-(n : ℝ) / (128 * T)) := by
  have hbound : uniformProbability (HasSparseOppositePrimePairs n T) ≤
      (concentrationPrimes T).card * Real.exp (-(n : ℝ) / (128 * T)) := by
    apply uniformProbability_exists_mem_le_card_mul
    intro q hq
    convert uniformProbability_selected_count_lt_le_exp (primeOppositePairs n q)
      (by linarith : 0 < T) (primeOppositePairs_card_ge hT hn hq) using 1
    exact congrArg (fun inst : Fintype (Fin ((n - 1) / 2) → Bool) ↦
      @uniformProbability _ inst (fun c ↦
        (selectedTrueCount (primeOppositePairs n q) c : ℝ) < (n : ℝ) / (32 * T)))
      (Subsingleton.elim _ _)
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (concentrationPrimes_card_le (by linarith)) (Real.exp_pos _).le)

end OdlyzkoPoonen
