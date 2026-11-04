import Formalization.Online.Regret.W1.OnlineW1ObservedPointwise
import Formalization.Online.Regret.W2.OnlineW2ObservedPointwise

/-! Same-experiment suffix proof component: OnlineW12AbsolutePointwise.
Scope and source confidence are established only by the final applying theorem. -/
namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w12AbsState : DecidableEq State := Classical.decEq State
noncomputable local instance w12AbsAction : DecidableEq Action := Classical.decEq Action

theorem onlineObservedW1_pointwise_abs_bound
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State))
    (k : Fin K) (h : Fin H) (s : State) (a : Action) (δ : ℝ)
    (hcert : onlineObservedTrueW1Certificates H K E δ history) :
    let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
    let row := (h, (s, a))
    let n := (onlineRowOutcomes (history.take (k.val * H)) row).length
    let v := onlineTrueSuffixRowFamily E row
    |(onlineObservedPlanningRow stage s a).expectation v - ((E h).transition s a).expectation v| ≤
      if 3 ≤ n then onlineTrueW1Radius (H : ℝ) δ n ((E h).transition s a) v else H := by
  classical
  let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
  let row : OnlineMDPRow State Action H := (h, (s, a))
  let n := (onlineRowOutcomes (history.take (k.val * H)) row).length
  let v := onlineTrueSuffixRowFamily E row
  change |(onlineObservedPlanningRow stage s a).expectation v - ((E h).transition s a).expectation v| ≤
      if 3 ≤ n then onlineTrueW1Radius (H : ℝ) δ n ((E h).transition s a) v else H
  by_cases hn : 3 ≤ n
  · have hp : 0 < (stage.observations s a).length := by change 0 < n; omega
    have hrow := onlineObservedPlanningRow_positive stage s a hp
    have heq : onlineObservedPlanningRow stage s a = FiniteDistribution.empiricalRow n (by omega)
        (onlineObservedRowData (history.take (k.val * H)) row) := by
      simpa [stage, row, n, onlineHistoryPlanningStage, onlineObservedRowData] using hrow
    have hb := hcert k row hn
    rw [heq]
    simpa only [if_pos hn] using hb
  · have hb := onlineTrueW1_bounded_error ((E h).transition s a)
      (onlineObservedPlanningRow stage s a) v (H : ℝ) (onlineTrueSuffixRowFamily_range H E row)
    simpa only [if_neg hn] using hb

/-- The existing coordinate bound yields both signs: apply it also to H−V.
This uses the same coordinate certificate and the same true-row variance. -/
theorem onlineW2_weighted_coordinate_abs_bound
    (p q : FiniteDistribution State) (V : State → ℝ) (H L N : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hN : 0 < N)
    (hV : ∀ x, 0 ≤ V x ∧ V x ≤ H)
    (hcoord : ∀ x, |q.prob x - p.prob x| ≤
      Real.sqrt (2 * p.prob x * L / N) + L / N) :
    |q.expectation V - p.expectation V| ≤
      Real.sqrt (2 * (Fintype.card State : ℝ) * L / N) * Real.sqrt (p.variance V) +
      (Fintype.card State : ℝ) * H * L / N := by
  have hp := onlineW2_weighted_coordinate_bound p q V H L N hH hL hN hV hcoord
  have hflip : ∀ x, 0 ≤ H - V x ∧ H - V x ≤ H := fun x => by constructor <;> linarith [(hV x).1, (hV x).2]
  have hn := onlineW2_weighted_coordinate_bound p q (fun x => H - V x) H L N hH hL hN hflip hcoord
  rw [p.variance_const_sub V H] at hn
  simp only [FiniteDistribution.expectation_sub, FiniteDistribution.expectation_const] at hn
  exact abs_le.mpr ⟨by linarith, hp⟩
end StatisticalRL.OnlineRL

namespace StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w12ObservedState : DecidableEq State := Classical.decEq State
noncomputable local instance w12ObservedAction : DecidableEq Action := Classical.decEq Action

/-- Two-sided coordinate envelope at one actual pre-episode row. -/
theorem onlineObservedW2_pointwise_abs_bound
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action)
    (history : List (OnlineMDPRow State Action H × State))
    (k : Fin K) (h : Fin H) (s : State) (a : Action) (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5)
    (hcert : onlineObservedW2CoordinateCertificates H K E δ history)
    (V : State → ℝ) (hV : ∀ x, 0 ≤ V x ∧ V x ≤ H) :
    let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
    let row := (h, (s, a))
    let n := (onlineRowOutcomes (history.take (k.val * H)) row).length
    |(onlineObservedPlanningRow stage s a).expectation V - ((E h).transition s a).expectation V| ≤
      if 3 ≤ n then
        Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n) *
          Real.sqrt (((E h).transition s a).variance V) +
        (Fintype.card State : ℝ) * H * Real.log (1 / δ) / n else H := by
  classical
  let stage := onlineHistoryPlanningStage E (history.take (k.val * H)) h
  let row : OnlineMDPRow State Action H := (h, (s, a))
  let n := (onlineRowOutcomes (history.take (k.val * H)) row).length
  change |(onlineObservedPlanningRow stage s a).expectation V - ((E h).transition s a).expectation V| ≤
      if 3 ≤ n then _ else _
  by_cases hn : 3 ≤ n
  · have hp : 0 < (stage.observations s a).length := by change 0 < n; omega
    have hrow := onlineObservedPlanningRow_positive stage s a hp
    have heq : onlineObservedPlanningRow stage s a = FiniteDistribution.empiricalRow n (by omega)
        (onlineObservedRowData (history.take (k.val * H)) row) := by
      simpa [stage, row, n, onlineHistoryPlanningStage, onlineObservedRowData] using hrow
    have hL : 0 ≤ Real.log (1 / δ) := by
      apply Real.log_nonneg
      apply (one_le_div hδ).2
      linarith
    have hb := onlineW2_weighted_coordinate_abs_bound ((E h).transition s a)
      (FiniteDistribution.empiricalRow n (by omega) (onlineObservedRowData (history.take (k.val * H)) row))
      V H (Real.log (1 / δ)) n (by positivity) hL (by exact_mod_cast (show 0 < n by omega)) hV
      (fun x => onlineObservedW2_selected_coordinate_bound H K E δ hδ hδsmall history hcert k row hn x)
    rw [heq]
    simpa only [if_pos hn] using hb
  · have hb := onlineTrueW1_bounded_error ((E h).transition s a)
      (onlineObservedPlanningRow stage s a) V H hV
    simpa only [if_neg hn] using hb
end StatisticalRL.OnlineRL
