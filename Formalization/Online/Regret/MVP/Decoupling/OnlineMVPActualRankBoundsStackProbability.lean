import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualRankSquareRadius
import Formalization.Online.Regret.MVP.Model.OnlineMVPActualSampler

/-! Stack-law confidence for the actual data-dependent rank-error bounds.
This is expressed on the independent reset-vector/successor-stack experiment;
the path-based decoupling event is a separate consumer. -/
namespace StatisticalRL.OnlineRL

open MeasureTheory ProbabilityTheory
open StatisticalRL.FiniteHorizonGenerative
open StatisticalRL.OnlineRL.MVPProfile
open scoped BigOperators

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance mvpRankBoundsStackProbabilityStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance mvpRankBoundsStackProbabilityStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpRankBoundsStackProbabilityActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The event that the fixed actual committed planner's linear and squared
rank-error sums satisfy their source bounds on one reset/stack sample. -/
noncomputable def mvpActualRankBoundsStackEvent
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (δ c₁ c₂ : ℝ) :
    Set ((Fin K → State) × (OnlineMDPRow State Action H × Fin K → State)) :=
  {sample |
    let δp := onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K
    let L := Real.log (1 / δp)
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback L c₁ c₂
    let rows := mvpActualRankRows hH sample.1 fallback planner sample.2
    let V := mvpActualRankValues hH E sample.1 fallback planner sample.2 L c₁ c₂
    let p := mvpActualRankTransition E
    let q0 := mvpActualRankInitial E hH
    let q1 := mvpActualRankFirst (by omega) sample.2
    let qb := mvpActualRankBatch sample.2
    let d := (Fintype.card (Fin H) : ℝ) * Fintype.card (State × Action)
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card (Fin H × (State × Action)))) * L
    let T := ∑ h : Fin H, ∑ k : Fin K,
      (p h (rows h k.val)).variance (V h k)
    (mvp_rankErrorTotal rows K V p q0 q1 qb ≤ Real.sqrt (d * I * T) + d * H * I) ∧
      (mvp_rankErrorTotal rows K (fun h k s => V h k s ^ 2) p q0 q1 qb ≤
        Real.sqrt (d * H^2 * I * T) + d * H^2 * I)}

/-- The actual independent reset/stack law satisfies both rank-error bounds
with the quarter-event confidence. The stack event remains a pointwise rank
consumer, not the path-based T1/W3/W4 event. -/
theorem mvp_actualRankBoundsStack_probability
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hbudget : (K : ℝ) ≥
      (Fintype.card (Fin H × (State × Action)) : ℝ) * logTwoReal K) :
    let δp := onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K
    1 - δp/2 ≤ (onlineMVPActualStackLaw E ρ K).real
      (mvpActualRankBoundsStackEvent hH hK E fallback δ c₁ c₂) := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let δp := onlineSourceOptimismDeltaPrime δ
    (Fintype.card State) (Fintype.card Action) H K
  let valueFamily := mvpActualValueSourceFamily (K := K) hH E
    (Real.log (1/δp)) c₁ c₂
  let squareFamily := mvpActualNormalizedSquareSourceFamily (K := K) hH E
    (Real.log (1/δp)) c₁ c₂
  let quarter := mvpQuarterStrongSourceUniformEvent hK E δ valueFamily ∩
    mvpQuarterStrongSourceUniformEvent hK E δ squareFamily
  let good : Set (Samples State Action H K) := {data | data ∈ quarter}
  let μ := onlineMVPActualStackLaw E ρ K
  let stackLaw := onlineMDPStackLaw E K
  change 1 - δp/2 ≤ μ.real (mvpActualRankBoundsStackEvent hH hK E fallback δ c₁ c₂)
  have hstate : 0 < Fintype.card State := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨Classical.choice (E ⟨0, hH⟩).state_nonempty⟩
  have haction : 0 < Fintype.card Action := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨Classical.choice (E ⟨0, hH⟩).action_nonempty⟩
  have hδp := mvp_correctedAllocation_domain_and_log δ
    (Fintype.card State) (Fintype.card Action) H K hδ hδ1 hstate haction hH (by omega)
  have hquarter := mvp_actualProfileFamilies_quarterStrong_intersection
    E hH hK δ c₁ c₂ hδ hδ1 hc₁ hc₂ hbudget
  have hgood : 1 - δp/2 ≤ (samplingLaw E K).real good := by
    simpa [δp, good, quarter, valueFamily, squareFamily,
      mvpActualValueSourceFamily, mvpActualNormalizedSquareSourceFamily] using hquarter.1
  have hlaw : stackLaw = samplingLaw E K := by
    dsimp [stackLaw, onlineMDPStackLaw, onlineStackProductLaw, samplingLaw,
      SampleIndex, OnlineMDPRow, onlineMDPSuccessorRowLaw]
  have hμprob : IsProbabilityMeasure μ := by
    dsimp [μ, onlineMVPActualStackLaw, onlineMDPInitialStackLaw, onlineMDPStackLaw]
    infer_instance
  have hlift : μ.real (Set.univ ×ˢ good) = (samplingLaw E K).real good := by
    dsimp [μ, onlineMVPActualStackLaw, onlineMDPInitialStackLaw]
    rw [measureReal_def, Measure.prod_prod, measure_univ, one_mul]
    change stackLaw.real good = (samplingLaw E K).real good
    exact congrArg (fun law : Measure (OnlineMDPRow State Action H × Fin K → State) => law.real good) hlaw
  have hsub : (Set.univ ×ˢ good) ⊆
      mvpActualRankBoundsStackEvent hH hK E fallback δ c₁ c₂ := by
    intro sample hs
    rcases sample with ⟨initial, data⟩
    have hboth : data ∈
        mvpQuarterStrongSourceUniformEvent hK E δ valueFamily ∩
          mvpQuarterStrongSourceUniformEvent hK E δ squareFamily := by
      simpa [good, quarter] using hs.2
    have hL : Real.log (1 / δp) =
        Real.log (1 / onlineSourceOptimismDeltaPrime δ
          (Fintype.card State) (Fintype.card Action) H K) := rfl
    have hbounds := mvp_actualRankLinearAndSquareBounds_of_quarterEvents
      hH hK E δ (Real.log (1/δp)) c₁ c₂ initial fallback
      (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂)
      data hδ hδ1 (by linarith) (by nlinarith [hc₂]) hL hboth.1 hboth.2
    simpa [mvpActualRankBoundsStackEvent, δp, valueFamily, squareFamily,
      mvpActualValueSourceFamily, mvpActualNormalizedSquareSourceFamily,
      mvpActualRankRows, mvpActualRankValues, mvpActualRankTransition,
      mvpActualRankInitial, mvpActualRankFirst, mvpActualRankBatch,
      onlineMVPCommittedGreedyPlanner] using hbounds
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  rw [hlift] at hmono
  exact le_trans hgood hmono

end StatisticalRL.OnlineRL
