import Formalization.Online.Regret.W3.OnlineW3ActualAdaptive

/-! Fixed optimal square error bound for any actual observed row. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w3FixedStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w3FixedActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineObservedW3_fixed_pointwise_bound
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State))
    (k : Fin K) (h : Fin H) (s : State) (a : Action) (δ : ℝ)
    (hcert : onlineObservedW3SquareCertificates H K E δ history) :
    let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
    let row := (h, (s, a))
    let n := (onlineRowOutcomes (history.take (k.val * H)) row).length
    let v := onlineW3SquaredTrueFamily H E row
    (onlineObservedPlanningRow stage s a).expectation v -
      ((E h).transition s a).expectation v ≤
      if 3 ≤ n then onlineTrueW1Radius ((H : ℝ)^2) δ n ((E h).transition s a) v else (H : ℝ)^2 := by
  classical
  let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
  let row : OnlineMDPRow State Action H := (h, (s, a))
  let n := (onlineRowOutcomes (history.take (k.val * H)) row).length
  let v := onlineW3SquaredTrueFamily H E row
  change (onlineObservedPlanningRow stage s a).expectation v -
      ((E h).transition s a).expectation v ≤
      if 3 ≤ n then onlineTrueW1Radius ((H : ℝ)^2) δ n ((E h).transition s a) v else (H : ℝ)^2
  by_cases hn : 3 ≤ n
  · have hp : 0 < (stage.observations s a).length := by change 0 < n; omega
    have hrow := onlineObservedPlanningRow_positive stage s a hp
    have hc := hcert k row hn
    change |(FiniteDistribution.empiricalRow n (by omega)
      (onlineObservedRowData (history.take (k.val * H)) row)).expectation v -
      (onlineMDPSuccessorRowLaw E row).expectation v| ≤
      onlineTrueW1Radius ((H : ℝ)^2) δ n (onlineMDPSuccessorRowLaw E row) v at hc
    have heq : onlineObservedPlanningRow stage s a = FiniteDistribution.empiricalRow n (by omega)
        (onlineObservedRowData (history.take (k.val * H)) row) := by
      simpa [stage, row, n, onlineHistoryPlanningStage, onlineObservedRowData] using hrow
    rw [heq]
    simp only [if_pos hn]
    exact (le_abs_self _).trans hc
  · have hb := onlineTrueW1_bounded_error ((E h).transition s a)
      (onlineObservedPlanningRow stage s a) v ((H : ℝ)^2) (onlineW3SquaredTrueFamily_range H E row)
    simp only [if_neg hn]
    exact (le_abs_self _).trans hb
end StatisticalRL.OnlineRL
