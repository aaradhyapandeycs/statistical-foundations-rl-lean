import Formalization.Online.Regret.MVP.Main.MVPMainSourceConfidence

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StatisticalRL.OnlineRL
universe uMvpRegret vMvpRegret

/-- Corrected explicit form of the MVP regret theorem, `thm-mvp-regret`,
`chapters/onlineRL.tex:1339–1352`. The source soft-O rate is made explicit
with a universal constant and the source polylogarithmic factor `max 1 I`.
This includes K=1 directly, where the printed proof factor I vanishes (C12).
Universal bonus witnesses are c₁=4,c₂=16; one fixed maximizing tie is used.
The algorithm uses the finite zero-count completion (C8), power-of-two
triggers (C13), and reciprocal confidence δp (C16), replacing the printed
numerator-100 allocation. The ceiling profile cover and terminal-zero
auxiliary family repair the proof gaps C15/C17. These are disclosed
corrections, not author approval of the printed formulas. The true value
of the same completed-history deployed policy defines each regret term.
-/
noncomputable def MVPSourceRegretCorrected : Prop :=
  ∃ C : ℝ, 0<C ∧
    ∀ (State : Type uMvpRegret) (Action : Type vMvpRegret)
      [Fintype State] [Fintype Action] (H K : ℕ) (hH : 0<H),
      0<K → ∀ (E : Fin H → EnvironmentStage State Action)
        (ρ : FiniteDistribution State) (δ : ℝ),
      0<δ → δ<1 →
      ∃ c₁ c₂ : ℝ, c₁=4 ∧ c₂=16 ∧ 0<c₁ ∧ 0<c₂ ∧
        let fallback : State := Classical.choice (E ⟨0,hH⟩).state_nonempty
        let S := Fintype.card State
        let A := Fintype.card Action
        let δp := δ/(100*(S:ℝ)^2*(A:ℝ)^2*(H:ℝ)^2*(K:ℝ)^2)
        let I := 40000*(Real.log K/Real.log 2)^3*
          Real.log (3*(S:ℝ)*A*H)*Real.log (1/δp)
        let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) c₁ c₂
        1-δ ≤ (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
          {sample : (Fin K → State) × OnlineOutcomePath.{uMvpRegret,0} State (K*H) |
            let history := onlineSequentialPathHistory
              (onlineEpisodicChoose H K hH sample.1 fallback planner) (K*H) [] sample.2
            (∑ k : Fin K,
              (DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E)) (sample.1 k) -
                DecisionStage.trajectoryValue
                  (List.ofFn (fun h : Fin H => (E h).withPolicy
                    (fun s => EnvironmentStage.pointMass (planner (history.take (k.val*H)) h s))))
                  (sample.1 k))) ≤
              C*max 1 I*min (Real.sqrt ((S:ℝ)*A*(H:ℝ)^3*K)) ((H:ℝ)*K)}

end StatisticalRL.OnlineRL

/- Apply the actual decoupling confidence bound. -/
namespace StatisticalRL.OnlineRL

theorem mvpSourceRegretCorrected_holds : MVPSourceRegretCorrected := by
  refine ⟨100, by norm_num, ?_⟩
  intro State Action _ _ H K hH hK E ρ δ hδ hδ1
  refine ⟨4, 16, rfl, rfl, by norm_num, by norm_num, ?_⟩
  simpa only [onlineSourceOptimismDeltaPrime, onlineW1SourceIota,
    mvpVarianceHistory] using
    (mvpMain_allK_expanded_source_confidence H K hH hK E ρ
      (Classical.choice (E ⟨0,hH⟩).state_nonempty) δ hδ hδ1)
end StatisticalRL.OnlineRL
