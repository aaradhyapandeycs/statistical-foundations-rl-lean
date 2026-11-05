import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPStackRankEventPairBounds
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPActualDecouplingEventPairBounds
import Formalization.Online.Regret.MVP.Decoupling.DecouplingImageTransport
import Formalization.Online.Regret.MVP.Decoupling.MVPDecouplingK1
import Formalization.Online.SourceOptimism.SourceOptimismAllocation
import Formalization.Online.Regret.MVP.MVPProfileDefinitions

/-! Actual stack-rank confidence transfers to the exact sequential decoupling
event. This source-facing consumer uses the fixed planner and source allocation. -/
namespace StatisticalRL.OnlineRL

open MeasureTheory ProbabilityTheory
open StatisticalRL.FiniteHorizonGenerative
open StatisticalRL.OnlineRL.MVPProfile

universe u v
variable {State : Type u} {Action : Type v} [Fintype State] [Fintype Action]

theorem mvp_actualDecouplingEvent_sourceConfidence
    (H K : ℕ) (hH : 0 < H) (hK : 1 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hbudget : (K : ℝ) ≥
      (Fintype.card (Fin H × (State × Action)) : ℝ) * logTwoReal K) :
    let δp := onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * Fintype.card (Fin H × (State × Action))) * Real.log (1 / δp)
    1 - δp < (onlineSequentialEpisodeLaw H K hH E ρ fallback
      (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δp)) c₁ c₂)
      (K * H)).rowMeasure.real
      (mvpActualDecouplingEvent H K hH E fallback δp c₁ c₂ I :
        Set ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H))) := by
  classical
  let S := Fintype.card State
  let A := Fintype.card Action
  let δp := onlineSourceOptimismDeltaPrime δ S A H K
  let I := 40000 * (Real.log K / Real.log 2)^3 *
    Real.log (3 * Fintype.card (Fin H × (State × Action))) * Real.log (1 / δp)
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback
    (Real.log (1 / δp)) c₁ c₂
  have hS : 0 < S := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨Classical.choice (E ⟨0, hH⟩).state_nonempty⟩
  have hA : 0 < A := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨Classical.choice (E ⟨0, hH⟩).action_nonempty⟩
  have hdomain := onlineSourceOptimismDeltaPrime_domain δ S A H K
    hδ hδ1 hS hA hH (by omega)
  have hδp : 0 < δp := by simpa [δp, S, A] using hdomain.1
  have hIone : 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * Fintype.card (Fin H × (State × Action))) * Real.log (1 / δp) = I := rfl
  have hKcase : K = 1 ∨ 2 ≤ K := by omega
  rcases hKcase with hKone | hKlarge
  · subst K
    have hIzero : I = 0 := by
      simp [I]
    have hUniv := mvpActualDecouplingEvent_one_episode_eq_univ
      H hH E fallback δp c₁ c₂
    have hEvent : mvpActualDecouplingEvent H 1 hH E fallback δp c₁ c₂ I = Set.univ := by
      simpa [hIzero] using hUniv
    have hprob : (onlineSequentialEpisodeLaw H 1 hH E ρ fallback planner (1 * H)).rowMeasure.real
        (mvpActualDecouplingEvent H 1 hH E fallback δp c₁ c₂ I) = 1 := by
      haveI : IsProbabilityMeasure
          (onlineSequentialEpisodeLaw H 1 hH E ρ fallback planner (1 * H)).rowMeasure := by
        infer_instance
      rw [hEvent, probReal_univ]
    change 1 - δp <
      (onlineSequentialEpisodeLaw H 1 hH E ρ fallback planner (1 * H)).rowMeasure.real
        (mvpActualDecouplingEvent H 1 hH E fallback δp c₁ c₂ I)
    rw [hprob]
    linarith [hδp]
  · let R := mvpActualRankBoundsStackEvent hH hKlarge E fallback δ c₁ c₂
    let Aevent := mvpActualDecouplingEvent H K hH E fallback δp c₁ c₂ I
    have hR : 1 - δp / 2 ≤ (onlineMDPInitialStackLaw E ρ K).real R := by
      simpa [R, δp, S, A] using
        (mvp_actualRankBoundsStack_probability hH hKlarge E ρ fallback δ c₁ c₂
          hδ hδ1 hc₁ hc₂ hbudget)
    have himage := onlineStack_rank_event_to_sequential_image_conditional
      H K hH E ρ fallback planner (K * H) le_rfl R Aevent δp hδp hR
      (by
        intro sample path hobs hmem
        have hreset : sample.1 = path.1 := congrArg Prod.fst hobs
        have htranscript :
            onlineSequentialPathHistory
              (onlineEpisodicChoose H K hH path.1 fallback planner)
              (K * H) [] path.2 =
            onlineMVPActualStackHistory hH sample.1 fallback planner sample.2 (K * H) := by
          have hsnd := congrArg Prod.snd hobs
          simpa [onlineMVPActualStackHistory] using hsnd.symm
        have hmem' : (path.1, sample.2) ∈ R := by
          have hsample : sample = (path.1, sample.2) := Prod.ext hreset rfl
          rw [← hsample]
          exact hmem
        have htranscript' :
            onlineSequentialPathHistory
              (onlineEpisodicChoose H K hH path.1 fallback
                (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δp)) c₁ c₂))
              (K * H) [] path.2 =
            onlineMVPActualStackHistory hH sample.1 fallback
              (onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1 / δp)) c₁ c₂)
              sample.2 (K * H) := by
          simpa only [planner] using htranscript
        have htranscript'' := htranscript'
        rw [hreset] at htranscript''
        have hpair := mvpActualRankBoundsStackEvent_pairBounds
          hH hKlarge E fallback δ c₁ c₂ (path.1, sample.2) hmem'
        have hpairEvent := mvpActualDecouplingEvent_of_pairRankBounds
          hH (by omega) E path.1 fallback sample.2 path.2 δp c₁ c₂ I
          htranscript'' hpair.1 hpair.2
        change (path.1, path.2) ∈ Aevent
        exact hpairEvent)
    change 1 - δp <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real Aevent
    exact himage

end StatisticalRL.OnlineRL
