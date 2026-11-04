import Formalization.Online.Regret.T2.OnlineT2ActualAlignment
import Formalization.Online.Regret.T2.OnlineT2ActualCountBudget
import Formalization.Online.Regret.T2.OnlineT2FirstVisits
import Formalization.Online.Regret.T2.OnlineT2ChargeAggregation
import Formalization.Online.Regret.W1.OnlineW1ActualRadiusAlignment

/-! Actual-path deterministic T₂ charge bound using observed empirical T₅,
zero-count first visits and positive-count ranks. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance t2CoarseStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t2CoarseActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineActualT2_le_coarseBudget
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) (hL : 0 ≤ Real.log (1 / δ)) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    let A := (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H
    let B := Real.log K / Real.log 2
    let L := Real.log (1 / δ)
    onlineActualT2 H K hH E initial fallback path δ c₁ c₂ ≤
      H * A + c₁ * Real.sqrt (2 * A * B * L * onlineActualT5 H K hH E initial fallback path δ c₁ c₂) +
        2 * c₂ * H * A * B * L := by
  classical
  let A := (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H
  let B := Real.log K / Real.log 2
  let L := Real.log (1 / δ)
  let planner := onlineCappedGreedyPlanner E L c₁ c₂
  let history := onlineSequentialPathHistory (onlineEpisodicChoose H K hH initial fallback planner) (K * H) [] path
  let count := fun i : Fin H × Fin K => onlineActualW1Count H K hH E initial fallback path δ c₁ c₂ i.1 i.2
  let variance := fun i : Fin H × Fin K =>
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path i.1 i.2.val
    let stage := onlineHistoryPlanningStage E (history.take (i.2.val * H)) i.1
    let U := onlineActualOptimisticContinuation H K hH E initial fallback path δ c₁ c₂ i.1 i.2
    (onlineObservedPlanningRow stage sa.1 sa.2).variance U
  have hv : ∀ i, 0 ≤ variance i := fun i => FiniteDistribution.variance_nonneg _ _
  have hzero : (∑ i : Fin H × Fin K, if count i < 1 then (1 : ℝ) else 0) ≤ A := by
    have hh := onlineSequential_T2_firstVisits_le H K hH E initial fallback planner path
    simpa only [count, onlineActualW1Count, planner, L, A, Fintype.sum_prod_type, one_mul, mul_assoc] using hh
  have hinv : (∑ i : Fin H × Fin K, (count i : ℝ)⁻¹) ≤ 2 * A * B := by
    have hh := onlineSequential_T2_reciprocalCount_budget H K hH hK E initial fallback planner path
    have heq : (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * H *
        (2 * (Real.log K / Real.log 2)) = 2 * A * B := by dsimp [A, B]; ring
    simpa only [count, onlineActualW1Count, planner, L, heq, Fintype.sum_prod_type] using hh
  have hvar : (∑ i : Fin H × Fin K, variance i) = onlineActualT5 H K hH E initial fallback path δ c₁ c₂ := by
    simp [variance, planner, L, history, onlineActualT5, Fintype.sum_prod_type]
  have hagg := onlineT2_charge_sum_le (Finset.univ : Finset (Fin H × Fin K)) count variance H L c₁ c₂
    (by positivity) hL hc₁ hc₂ hv
  have hpoints : onlineActualT2 H K hH E initial fallback path δ c₁ c₂ =
      ∑ i : Fin H × Fin K, if 0 < count i then
        c₁ * Real.sqrt (variance i * L / count i) + c₂ * H * L / count i else H := by
    rw [onlineActualT2_eq_sum_points]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro k hk
    simp [onlineActualT2Point, onlineRegretAnalysisCharge, count, onlineActualW1Count,
      variance, planner, L, history, onlineHistoryPlanningStage]
  have hT5 : 0 ≤ onlineActualT5 H K hH E initial fallback path δ c₁ c₂ := by
    rw [← hvar]
    exact Finset.sum_nonneg (fun i hi => hv i)
  have hroot := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinv)
    (show 0 ≤ c₁ * Real.sqrt (L * onlineActualT5 H K hH E initial fallback path δ c₁ c₂) by positivity)
  have hsmall := mul_le_mul_of_nonneg_left hzero (show (0 : ℝ) ≤ H by exact_mod_cast Nat.zero_le H)
  have hlin := mul_le_mul_of_nonneg_left hinv (show 0 ≤ c₂ * H * L by positivity)
  have hfactor : Real.sqrt (L * onlineActualT5 H K hH E initial fallback path δ c₁ c₂) * Real.sqrt (2 * A * B) =
      Real.sqrt (2 * A * B * L * onlineActualT5 H K hH E initial fallback path δ c₁ c₂) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ L * onlineActualT5 H K hH E initial fallback path δ c₁ c₂)]
    congr 1
    ring
  rw [← hpoints, hvar] at hagg
  change _ ≤ (H : ℝ) * A + c₁ * Real.sqrt (2 * A * B * L * onlineActualT5 H K hH E initial fallback path δ c₁ c₂) + 2 * c₂ * H * A * B * L
  rw [← hfactor]
  nlinarith
end StatisticalRL.OnlineRL
