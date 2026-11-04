import Formalization.Online.Regret.W2.OnlineW2ObservedRadiusConsumer
import Formalization.Online.Regret.W1.OnlineW1ObservedPointwise

/-! Conditional actual planning-row W₂ estimate. Continuation range is an
intermediate premise to be discharged by actual optimism and value bounds. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w2PointwiseStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w2PointwiseActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The same pre-episode row used by the algorithm satisfies the coordinate
bound when its count is at least three, and a bounded-error estimate otherwise. -/
theorem onlineObservedW2_pointwise_bound
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State))
    (k : Fin K) (h : Fin H) (s : State) (a : Action) (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5)
    (hcert : onlineObservedW2CoordinateCertificates H K E δ history)
    (V : State → ℝ) (hV : ∀ x, 0 ≤ V x ∧ V x ≤ H) :
    let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
    let row := (h, (s, a))
    let n := (onlineRowOutcomes (history.take (k.val * H)) row).length
    (onlineObservedPlanningRow stage s a).expectation V -
      ((E h).transition s a).expectation V ≤
      if 3 ≤ n then
        Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n) *
          Real.sqrt (((E h).transition s a).variance V) +
        (Fintype.card State : ℝ) * H * Real.log (1 / δ) / n else H := by
  classical
  let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
  let row : OnlineMDPRow State Action H := (h, (s, a))
  let n := (onlineRowOutcomes (history.take (k.val * H)) row).length
  change (onlineObservedPlanningRow stage s a).expectation V -
      ((E h).transition s a).expectation V ≤
      if 3 ≤ n then
        Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n) *
          Real.sqrt (((E h).transition s a).variance V) +
        (Fintype.card State : ℝ) * H * Real.log (1 / δ) / n else H
  by_cases hn : 3 ≤ n
  · have hp : 0 < (stage.observations s a).length := by
      change 0 < n
      omega
    have hrow := onlineObservedPlanningRow_positive stage s a hp
    have heq : onlineObservedPlanningRow stage s a = FiniteDistribution.empiricalRow n (by omega)
        (onlineObservedRowData (history.take (k.val * H)) row) := by
      simpa [stage, row, n, onlineHistoryPlanningStage, onlineObservedRowData] using hrow
    have hb := onlineObservedW2_selected_weighted_bound H K E δ hδ hδsmall
      history hcert k row hn V hV
    rw [heq]
    simp only [if_pos hn]
    exact hb
  · have hb := onlineTrueW1_bounded_error ((E h).transition s a)
      (onlineObservedPlanningRow stage s a) V (H : ℝ) hV
    simp only [if_neg hn]
    exact (le_abs_self _).trans hb
end StatisticalRL.OnlineRL
