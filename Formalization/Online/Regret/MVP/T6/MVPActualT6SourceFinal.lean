import Formalization.Online.Regret.MVP.T6.MVPActualT6LargeConfidence
import Formalization.Online.Regret.MVP.T6.MVPActualT6K1Bound
import Formalization.Online.SourceOptimism.SourceOptimismAllocation

/-! Corrected source allocation and all K≥1 for `lem:bound-T6-ucb-mvp`.
The event is on the actual MVP sequential law and has no bound premise. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]
local instance t6MVPActualT6SourceFinal_mvpT6FinalState : MeasurableSpace State := ⊤
local instance t6MVPActualT6SourceFinal_mvpT6FinalSample (H K : ℕ) : MeasurableSpace
  ((Fin K → State) × OnlineOutcomePath.{u,0} State (K*H)) := ⊤

theorem mvpActualT6_source_confidence (H K : ℕ) (hH : 0<H) (hK : 0<K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1)
    (hc₁ : 4≤c₁) (hc₂ : c₁^2≤c₂) :
    let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂
    1-4*(Fintype.card State : ℝ)*Fintype.card Action*H*K*δp ≤
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        (mvpT6SourceEvent H K hH E fallback δp c₁ c₂) := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  have hS : 0<Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
  have hA : 0<Fintype.card Action := Fintype.card_pos_iff.mpr inferInstance
  let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  have hd := onlineSourceOptimismDeltaPrime_domain δ (Fintype.card State) (Fintype.card Action)
    H K hδ hδ1 hS hA hH hK
  have hδp : 0<δp := hd.1
  have hL : 0 ≤ Real.log (1/δp) := by
    have := onlineSmallConfidence_log_ge_one δp hd.1 hd.2
    linarith
  have hc₁0 : 0≤c₁ := by linarith
  have hc₂0 : 0≤c₂ := by nlinarith [sq_nonneg c₁]
  by_cases hK2 : 2≤K
  · exact mvpActualT6_large_confidence H K hH hK2 E ρ fallback δp c₁ c₂ hd.1 hd.2 hc₁0 hc₂0
  · have hOne : K=1 := by omega
    subst K
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂
    let μ := (onlineSequentialEpisodeLaw H 1 hH E ρ fallback planner (1*H)).rowMeasure
    letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
    have hall : mvpT6SourceEvent H 1 hH E fallback δp c₁ c₂ = Set.univ := by
      apply Set.eq_univ_of_forall
      intro sample
      simpa only [mvpT6SourceEvent, Set.mem_setOf_eq, Nat.cast_one, one_mul] using
        mvp_actualT6_one_episode_bound H hH E sample.1 fallback sample.2 δp c₁ c₂ hL hc₁0 hc₂0
    change 1-4*(Fintype.card State : ℝ)*Fintype.card Action*H*(1:ℕ)*δp ≤ μ.real _
    rw [hall, probReal_univ]
    have hnonneg : 0 ≤ 4*(Fintype.card State : ℝ)*Fintype.card Action*H*(1:ℕ)*δp := by positivity
    linarith
end StatisticalRL.OnlineRL
