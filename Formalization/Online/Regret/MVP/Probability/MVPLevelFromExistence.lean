import Formalization.Online.Regret.MVP.Probability.MVPDyadicLevel

/-! Any noninitial source level implies at least two episodes. -/
namespace StatisticalRL.OnlineRL

theorem mvpUniformLevel_K_ge_two {K : ℕ} (l : mvpUniformLevel K) : 2 ≤ K := by
  by_cases hz : K = 0
  · subst K
    exact Fin.elim0 l
  · have hl : 1 ≤ Nat.log2 K := by
      have h := l.isLt
      omega
    have hp := (Nat.le_log2 hz).1 hl
    simpa using hp

theorem mvpUniformBatchSize_fits_of_level {K : ℕ} (l : mvpUniformLevel K) :
    2 * mvpUniformBatchSize l ≤ K :=
  mvpUniformBatchSize_fits (mvpUniformLevel_K_ge_two l) l
end StatisticalRL.OnlineRL
