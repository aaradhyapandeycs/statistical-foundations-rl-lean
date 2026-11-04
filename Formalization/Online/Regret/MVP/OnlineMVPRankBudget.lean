import Formalization.Online.Regret.MVP.OnlineMVPActualVisitRanks
import Formalization.Online.Regret.MVP.OnlineMVPBlockBudget

/-! MVP count and deterministic visit-budget results. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem onlineMVP_storedReciprocal_block (j : ℕ) (hj : 1 ≤ j) :
    (∑ n ∈ Finset.Ico (2^j) (2^(j+1)), onlineMVPStoredReciprocal n) = 2 := by
  calc
    _ = ∑ _n ∈ Finset.Ico (2^j) (2^(j+1)), (1 : ℝ) / (2^(j-1) : ℕ) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hlo := (Finset.mem_Ico.mp hn).1
      have hhi := (Finset.mem_Ico.mp hn).2
      have hlog := onlineMVP_log2_eq_of_dyadic_bounds n j hlo hhi
      have hn2 : 2 ≤ n := by
        have hp : 2 ≤ 2^j := by
          calc
            2 = 2^1 := by norm_num
            _ ≤ 2^j := Nat.pow_le_pow_right (by decide) hj
        omega
      have hpow : 1 ≤ 2^(j-1) := Nat.one_le_pow (j-1) 2 (by decide)
      simp [onlineMVPStoredReciprocal, onlineMVP_storedCount_closedForm,
        Nat.not_lt.mpr hn2, hlog, max_eq_left hpow, one_div]
    _ = 2 := onlineMVP_full_dyadic_block_mass j hj

/-- For 2^(m+1) visits, ranks 0 and 1 contribute two and the next m
complete dyadic blocks contribute two each. -/
theorem onlineMVP_storedReciprocal_sum_power (m : ℕ) :
    (∑ n ∈ Finset.range (2^(m+1)), onlineMVPStoredReciprocal n) = 2 * (m+1) := by
  induction m with
  | zero =>
    have h0 : onlineMVPStoredCount 0 = 0 := by decide
    have h1 : onlineMVPStoredCount 1 = 1 := by decide
    norm_num [Finset.sum_range_succ, onlineMVPStoredReciprocal, h0, h1]
  | succ m ih =>
    have hle : 2^(m+1) ≤ 2^((m+1)+1) := by
      rw [Nat.pow_succ]
      omega
    rw [← Finset.sum_range_add_sum_Ico _ hle, ih,
      onlineMVP_storedReciprocal_block (m+1) (by omega)]
    push_cast
    ring

/-- Deterministic one-row prefix bound for the corrected batch interpretation;
the proof uses complete-block extension, not the false pointwise factor-two
comparison. -/
theorem onlineMVP_storedReciprocal_rank_bound (K : ℕ) (hK : 2 ≤ K) :
    (∑ n ∈ Finset.range K, onlineMVPStoredReciprocal n) ≤
      4 * (Real.log K / Real.log 2) := by
  let m := Nat.log2 (K-1)
  have hkpos : 0 < K := by omega
  have hpow : K ≤ 2^(m+1) := by
    have h := onlineMVP_lt_nextFloorPower (K-1)
    dsimp [m]
    omega
  have hsub : Finset.range K ⊆ Finset.range (2^(m+1)) := Finset.range_mono hpow
  have hsum : (∑ n ∈ Finset.range K, onlineMVPStoredReciprocal n) ≤
      ∑ n ∈ Finset.range (2^(m+1)), onlineMVPStoredReciprocal n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn hnot
    unfold onlineMVPStoredReciprocal
    positivity
  rw [onlineMVP_storedReciprocal_sum_power] at hsum
  have hlognat : Nat.log2 (K-1) ≤ Nat.log2 K := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right (by omega)
  have hlog := Real.log2_le_logb K
  have hlog1 : 1 ≤ Real.log K / Real.log 2 := by
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ K by exact_mod_cast hK)
  have hcast : (Nat.log2 (K-1) : ℝ) ≤ Nat.log2 K := by exact_mod_cast hlognat
  dsimp [m] at hsum
  simp only [Real.logb] at hlog
  nlinarith only [hsum, hcast, hlog, hlog1]
end StatisticalRL.OnlineRL
