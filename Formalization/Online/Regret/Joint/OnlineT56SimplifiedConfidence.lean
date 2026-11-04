import Formalization.Online.Regret.Joint.OnlineT56SimplifiedActual
import Formalization.Online.Regret.Joint.OnlineT56JointConditional
import Formalization.Online.Regret.Joint.OnlineW123Final

/-! Actual-law simplified T56 confidence consumer. The actual
first T56 event probability remains an explicit input. The W123 probability
is supplied by its proved same-law producer, never assumed independent. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance simpleConfidenceState : MeasurableSpace State := ⊤
noncomputable local instance simpleConfidenceSample (H K : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

noncomputable def onlineActualT56SimplifiedEvent
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δ c₁ c₂ : ℝ) :
    Set ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
  {sample |
    onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ c₁ c₂ ≤
      2*(K:ℝ)*(H:ℝ)^2 ∧
    onlineActualT5 H K hH E sample.1 fallback sample.2 δ c₁ c₂ ≤
      6*(K:ℝ)*(H:ℝ)^2 +
      (1/2:ℝ)*Real.sqrt ((Fintype.card State:ℝ)^2*Fintype.card Action*H^3*
        onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ c₁ c₂ *
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ) +
      4*(Fintype.card State:ℝ)^2*Fintype.card Action*H^3*
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ}

theorem onlineSourceAllocated_actualT56Complete_of_joint
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hI :
      let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
      8*max (c₁^2) c₂*(Real.log K/Real.log 2)*Real.log (1/δ') ≤
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ')
    (hlarge :
      let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
      (Fintype.card State:ℝ)*Fintype.card Action*H^2*
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ' ≤ (K:ℝ))
    (hjoint :
      let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
      let planner := onlineCappedGreedyPlanner E (Real.log (1/δ')) c₁ c₂
      1-14*(Fintype.card State:ℝ)^2*Fintype.card Action*H^2*K*δ' <
        (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
          (onlineActualT56JointEvent H K hH E fallback δ' c₁ c₂)) :
    let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineCappedGreedyPlanner E (Real.log (1/δ')) c₁ c₂
    1-30*(Fintype.card State:ℝ)^2*Fintype.card Action*H^2*K*δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        (onlineActualT56JointEvent H K hH E fallback δ' c₁ c₂ ∩
         onlineActualT56SimplifiedEvent H K hH E fallback δ' c₁ c₂) := by
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  let planner := onlineCappedGreedyPlanner E (Real.log (1/δ')) c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ];infer_instance
  have hd := onlineSourceOptimismDeltaPrime_domain δ (Fintype.card State)
    (Fintype.card Action) H K hδ hδone Fintype.card_pos Fintype.card_pos hH (by omega)
  have hδp : 0 < δ' := hd.1
  let first := onlineActualT56JointEvent H K hH E fallback δ' c₁ c₂
  let w123 := onlineActualW123RestrictedEvent H K hH E fallback δ' c₁ c₂
  have hw := onlineSourceAllocated_actualW123Restricted_strict H K hH hK E ρ fallback δ c₁ c₂ hδ hδone hc₁ hc₂
  have hi := onlineTwoEvent_confidence_strict μ first w123
    (14*(Fintype.card State:ℝ)^2*Fintype.card Action*H^2*K*δ')
    (12*(Fintype.card State:ℝ)^2*Fintype.card Action*H*K*δ') (le_of_lt hjoint) hw
  have hsub : first ∩ w123 ⊆ first ∩ onlineActualT56SimplifiedEvent H K hH E fallback δ' c₁ c₂ := by
    intro sample hs
    refine ⟨hs.1,?_⟩
    apply onlineActualT56_simplified_of_bounds H K hH hK E sample.1 fallback sample.2
      δ' c₁ c₂ hd.1 hd.2 hc₁ hc₂ hI hlarge hs.1.1
    · simpa only [mul_assoc] using hs.1.2.1
    · exact hs.2.2.2
  have hm := measureReal_mono (μ:=μ) hsub (measure_ne_top μ _)
  have hHr : (1:ℝ) ≤ H := by exact_mod_cast (Nat.succ_le_iff.mpr hH)
  have hHsq : (H:ℝ) ≤ (H:ℝ)^2 := by
    have hp := mul_nonneg (show (0:ℝ) ≤ H by positivity) (sub_nonneg.mpr hHr)
    nlinarith only [hp]
  let B := (Fintype.card State:ℝ)^2*(Fintype.card Action:ℝ)*K*δ'
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hb := mul_le_mul_of_nonneg_left hHsq (show 0 ≤ 12*B by positivity)
  have hb2 := mul_nonneg hB (sq_nonneg (H:ℝ))
  have hscalar : 14*B*(H:ℝ)^2+12*B*H ≤ 30*B*H^2 := by nlinarith only [hb,hb2]
  have hmargin :
      1-30*(Fintype.card State:ℝ)^2*Fintype.card Action*H^2*K*δ' ≤
      1-(14*(Fintype.card State:ℝ)^2*Fintype.card Action*H^2*K*δ' +
         12*(Fintype.card State:ℝ)^2*Fintype.card Action*H*K*δ') := by
    dsimp only [B] at hscalar
    nlinarith only [hscalar]
  exact hmargin.trans_lt (hi.trans_le hm)

end StatisticalRL.OnlineRL
