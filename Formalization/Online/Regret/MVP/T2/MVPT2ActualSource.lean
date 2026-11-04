import Formalization.Online.Regret.MVP.MVPT2Definitions
import Formalization.Online.Regret.MVP.T2.MVPT2ActualCount
import Formalization.Online.Regret.MVP.T2.MVPT2CountAggregation
import Formalization.Online.Regret.MVP.T2.MVPT2Scalar
import Formalization.Online.Regret.MVP.T2.MVPT2Iota
import Formalization.Online.Regret.MVP.MVPVarianceDefinitions

/-! Source-facing MVP T2 candidate. Its only coefficient choice is
the source theorem's suitable fixed pair (4,16); no visit-budget premise. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpT2SourceStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpT2SourceActionDecidable : DecidableEq Action := Classical.decEq Action


theorem mvpActualT2_le_sourceBound_fixed
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K*H))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp
    mvpVarianceT2 H K hH E initial fallback path δp 4 16 ≤
      (1 / 2 : ℝ) * Real.sqrt ((Fintype.card State : ℝ) * Fintype.card Action * H *
        mvpActualT5 H K hH E initial fallback path δp 4 16 * I) +
      (1 / 2 : ℝ) * (Fintype.card State : ℝ) * Fintype.card Action * H^2 * I := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp
  let A := (Fintype.card State : ℝ) * Fintype.card Action * H
  let B := Real.log K / Real.log 2
  let L := Real.log (1/δp)
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback L 4 16
  let history := mvpVarianceHistory H K hH E initial fallback path δp 4 16
  let count := fun i : Fin H × Fin K => mvpT2ActualRetainedCount H K hH E initial fallback planner path i.1 i.2
  let variance := fun i : Fin H × Fin K =>
    let sa := onlineActualStageRowSequence H K hH initial fallback planner path i.1 i.2.val
    let hist := history.take (i.2.val*H)
    letI : Nonempty State := (E i.1).state_nonempty
    let stage := onlineMVPActualPlanningStage E (onlineMVPHistoryRowAt hH E fallback hist)
      (onlineMVPHistoryNextAt fallback hist) hist.length i.1
    (onlineObservedPlanningRow stage sa.1 sa.2).variance
      (mvpVarianceContinuation H K hH E initial fallback path δp 4 16 i.1 i.2)
  have hd := mvp_correctedAllocation_domain_and_log δ (Fintype.card State) (Fintype.card Action) H K
    hδ hδ1 Fintype.card_pos Fintype.card_pos hH (by omega)
  have hL : 0 ≤ L := by dsimp [L, δp]; linarith [hd.2.2]
  have hv : ∀ i, 0 ≤ variance i := fun i => FiniteDistribution.variance_nonneg _ _
  have hbudget : (∑ i : Fin H × Fin K, (((max (count i) 1 : ℕ) : ℝ)⁻¹)) ≤ 4*A*B := by
    have hb := mvpT2_actual_retainedReciprocal_budget H K hH hK E initial fallback planner path
    simpa [count, A, B, Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm] using hb
  have hvar : (∑ i : Fin H × Fin K, variance i) = mvpActualT5 H K hH E initial fallback path δp 4 16 := by
    simp [variance, planner, L, history, mvpActualT5, Fintype.sum_prod_type]
  have hpoints : mvpVarianceT2 H K hH E initial fallback path δp 4 16 =
      ∑ i : Fin H × Fin K, if 0 < count i then
        4 * Real.sqrt (variance i * L / count i) + 16 * H * L / count i else H := by
    simp [mvpVarianceT2, onlineRegretAnalysisCharge, count, mvpT2ActualRetainedCount,
      variance, planner, L, history, mvpVarianceHistory, Fintype.sum_prod_type]
  have ha := mvpT2_charge_sum_le_maxOne (Finset.univ : Finset (Fin H × Fin K)) count variance H L 4 16 (4*A*B)
    (by positivity) hL (by norm_num) (by norm_num) hv (by simpa using hbudget)
  have hT : 0 ≤ mvpActualT5 H K hH E initial fallback path δp 4 16 := by
    rw [← hvar]; exact Finset.sum_nonneg (fun i hi => hv i)
  have hB : 0 ≤ B := by
    dsimp [B]; exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ K by omega))) (le_of_lt (Real.log_pos (by norm_num)))
  have hfactor : Real.sqrt (L * mvpActualT5 H K hH E initial fallback path δp 4 16) * Real.sqrt (4*A*B) =
      Real.sqrt (4*A*B*L*mvpActualT5 H K hH E initial fallback path δp 4 16) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ L * mvpActualT5 H K hH E initial fallback path δp 4 16)]
    congr 1; ring
  have hcoarse : mvpVarianceT2 H K hH E initial fallback path δp 4 16 ≤
      4*A*H*B + 4*Real.sqrt (4*A*B*L*mvpActualT5 H K hH E initial fallback path δp 4 16) +
      4*16*H*A*B*L := by
    rw [← hpoints, hvar, hfactor] at ha
    nlinarith
  have hi := mvpT2_fixed_iota_conditions (Fintype.card State) (Fintype.card Action) H K δ
    Fintype.card_pos Fintype.card_pos hH hK hδ hδ1
  have hs := mvpT2_coarse_to_source A H B L I 4 16 (mvpActualT5 H K hH E initial fallback path δp 4 16)
    (by positivity) (by positivity) hB hL (by norm_num) (by norm_num) hT hi.1 hi.2
  apply le_trans hcoarse
  convert hs using 1 <;> dsimp [A, I] <;> ring
end StatisticalRL.OnlineRL
