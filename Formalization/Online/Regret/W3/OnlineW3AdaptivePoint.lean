import Formalization.Online.Regret.W3.OnlineW3ActualAdaptive
import Formalization.Online.Regret.W2.OnlineW2ObservedRadiusConsumer

/-! Adaptive W₃ pointwise bound from the SAME all-coordinate event as W₂.
No conditional independence of the adaptive continuation is asserted. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w3AdaptPointStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w3AdaptPointActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineObservedW3_adaptive_pointwise_bound
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State))
    (k : Fin K) (h : Fin H) (s : State) (a : Action) (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5)
    (hcert : onlineObservedW2CoordinateCertificates H K E δ history)
    (V : State → ℝ) (hV : ∀ x, 0 ≤ V x ∧ V x ≤ (H : ℝ)^2) :
    let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
    let row := (h, (s, a))
    let n := (onlineRowOutcomes (history.take (k.val * H)) row).length
    (onlineObservedPlanningRow stage s a).expectation V -
      ((E h).transition s a).expectation V ≤
      if 3 ≤ n then
        Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n) *
          Real.sqrt (((E h).transition s a).variance V) +
        (Fintype.card State : ℝ) * (H : ℝ)^2 * Real.log (1 / δ) / n else (H : ℝ)^2 := by
  classical
  let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
  let row : OnlineMDPRow State Action H := (h, (s, a))
  let n := (onlineRowOutcomes (history.take (k.val * H)) row).length
  change (onlineObservedPlanningRow stage s a).expectation V -
      ((E h).transition s a).expectation V ≤
      if 3 ≤ n then
        Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n) *
          Real.sqrt (((E h).transition s a).variance V) +
        (Fintype.card State : ℝ) * (H : ℝ)^2 * Real.log (1 / δ) / n else (H : ℝ)^2
  have hL : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    apply (one_le_div hδ).2
    linarith
  by_cases hn : 3 ≤ n
  · have hp : 0 < (stage.observations s a).length := by change 0 < n; omega
    have hrow := onlineObservedPlanningRow_positive stage s a hp
    have heq : onlineObservedPlanningRow stage s a = FiniteDistribution.empiricalRow n (by omega)
        (onlineObservedRowData (history.take (k.val * H)) row) := by
      simpa [stage, row, n, onlineHistoryPlanningStage, onlineObservedRowData] using hrow
    have hc : ∀ x, |(FiniteDistribution.empiricalRow n (by omega)
        (onlineObservedRowData (history.take (k.val * H)) row)).prob x -
        (onlineMDPSuccessorRowLaw E row).prob x| ≤
        Real.sqrt (2 * (onlineMDPSuccessorRowLaw E row).prob x * Real.log (1 / δ) / n) +
          Real.log (1 / δ) / n := by
      intro x
      exact onlineObservedW2_selected_coordinate_bound H K E δ hδ hδsmall history hcert k row hn x
    have hb := onlineW2_weighted_coordinate_bound (onlineMDPSuccessorRowLaw E row)
      (FiniteDistribution.empiricalRow n (by omega) (onlineObservedRowData (history.take (k.val * H)) row))
      V ((H : ℝ)^2) (Real.log (1 / δ)) n (sq_nonneg _) hL (by exact_mod_cast (show 0 < n by omega)) hV hc
    rw [heq]
    simp only [if_pos hn]
    exact hb
  · have hb := onlineTrueW1_bounded_error ((E h).transition s a)
      (onlineObservedPlanningRow stage s a) V ((H : ℝ)^2) hV
    simp only [if_neg hn]
    exact (le_abs_self _).trans hb
end StatisticalRL.OnlineRL
