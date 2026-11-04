import Formalization.Online.Regret.W1.OnlineW1TrueVariancePrefix
import Formalization.Online.Regret.W1.W1Definitions

/-! OnlineW1ObservedPointwise: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance OnlineW1ObservedPointwiseLocalInstance1 : DecidableEq State := Classical.decEq State
noncomputable local instance OnlineW1ObservedPointwiseLocalInstance2 : DecidableEq Action := Classical.decEq Action

/-- A single played stage of a completed history consumes the two-sided
certificate for its actual row. -/
theorem onlineObservedW1_pointwise_bound
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State))
    (k : Fin K) (h : Fin H) (s : State) (a : Action) (δ : ℝ)
    (hcert : onlineObservedTrueW1Certificates H K E δ history) :
    let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
    let row := (h, (s, a))
    let n := (onlineRowOutcomes (history.take (k.val * H)) row).length
    let v := onlineTrueSuffixRowFamily E row
    (onlineObservedPlanningRow stage s a).expectation v -
      ((E h).transition s a).expectation v ≤
      if 3 ≤ n then onlineTrueW1Radius (H : ℝ) δ n ((E h).transition s a) v else H := by
  classical
  let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
  let row : OnlineMDPRow State Action H := (h, (s, a))
  let n := (onlineRowOutcomes (history.take (k.val * H)) row).length
  let v := onlineTrueSuffixRowFamily E row
  change (onlineObservedPlanningRow stage s a).expectation v -
      ((E h).transition s a).expectation v ≤
      if 3 ≤ n then onlineTrueW1Radius (H : ℝ) δ n ((E h).transition s a) v else H
  by_cases hn : 3 ≤ n
  · have hp : 0 < (stage.observations s a).length := by
      change 0 < n
      omega
    have hrow := onlineObservedPlanningRow_positive stage s a hp
    have h := hcert k row hn
    change |(FiniteDistribution.empiricalRow n (by omega)
      (onlineObservedRowData (history.take (k.val * H)) row)).expectation v -
      (onlineMDPSuccessorRowLaw E row).expectation v| ≤
      onlineTrueW1Radius (H : ℝ) δ n (onlineMDPSuccessorRowLaw E row) v at h
    have heq : onlineObservedPlanningRow stage s a = FiniteDistribution.empiricalRow n (by omega)
        (onlineObservedRowData (history.take (k.val * H)) row) := by
      simpa [stage, row, n, onlineHistoryPlanningStage, onlineObservedRowData] using hrow
    rw [heq]
    simp only [if_pos hn]
    exact (le_abs_self _).trans h
  · have h := onlineTrueW1_bounded_error ((E h).transition s a)
      (onlineObservedPlanningRow stage s a) v (H : ℝ) (onlineTrueSuffixRowFamily_range H E row)
    simp only [if_neg hn]
    exact (le_abs_self _).trans h
end StatisticalRL.OnlineRL
