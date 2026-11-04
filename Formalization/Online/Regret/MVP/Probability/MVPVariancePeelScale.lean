import Formalization.Online.Regret.MVP.Probability.MVPDyadicLevel

/-! A source-sized dyadic peeling index covers all actual batch variances. -/
namespace StatisticalRL.OnlineRL

def mvpUniformPeels (d K : ℕ) : ℕ := Nat.log2 (d*K) + 1

theorem mvpUniformPeels_pos (d K : ℕ) : 0 < mvpUniformPeels d K := by
  simp [mvpUniformPeels]

theorem mvpUniformPeels_cover (d K n : ℕ) (hn : n ≤ K) :
    n*d ≤ 2^(mvpUniformPeels d K) := by
  have hpow : d*K < 2^(mvpUniformPeels d K) := by
    unfold mvpUniformPeels
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) _
  have hmul : n*d ≤ d*K := by nlinarith
  exact le_of_lt (lt_of_le_of_lt hmul hpow)
end StatisticalRL.OnlineRL
