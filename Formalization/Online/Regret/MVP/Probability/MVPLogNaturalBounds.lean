import Formalization.Online.Regret.MVP.Probability.MVPVariancePeelScale

/-! Natural cardinal and peeling bounds needed by the profile union. -/
namespace StatisticalRL.OnlineRL

theorem mvp_log2_le_K (K : ℕ) : Nat.log2 K ≤ K := by
  rw [Nat.log2_eq_log_two]
  exact Nat.log_le_self 2 K

theorem mvpUniformPeels_le (d K : ℕ) (hd : 1 ≤ d) (hK : 2 ≤ K) :
    mvpUniformPeels d K ≤ d*K := by
  have hpos : d*K ≠ 0 := by positivity
  have h := Nat.log_lt_self 2 hpos
  rw [← Nat.log2_eq_log_two] at h
  unfold mvpUniformPeels
  omega
end StatisticalRL.OnlineRL
