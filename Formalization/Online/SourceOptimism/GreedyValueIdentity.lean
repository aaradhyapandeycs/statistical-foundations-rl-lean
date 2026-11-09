import Formalization.Online.SourceOptimism.CappedGreedyPlannerDefinitions
import Formalization.Online.Regret.Main.OnlineUCBVIRegretMain

/-! The greedy identity `V_h(s) = max_a Q_h(s,a) = Q_h(s, π_h(s))` of Remark 5.5
(`chapters/onlineRL.tex:790–802`) for the corrected UCBVI tables, and the burn-in
form of the UCBVI regret bound (`eq:burn-in-ucbvi`, `eq:regret-asymptotic-ucbvi`,
`chapters/onlineRL.tex:491–506`). -/

namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]

/-- At every stage of the completed-history tables, the value is the maximum of the
Q row, and the greedy planner attains it. -/
theorem onlineCappedBackward_greedy_identity {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (L c₁ c₂ : ℝ)
    (history : List (OnlineMDPRow State Action H × State)) (h : Fin H) (s : State) :
    letI : Nonempty Action := (E h).action_nonempty
    let stages := onlineCompletedHistoryPlanningStages E history
    onlineCappedBackwardValueAt (H : ℝ) L c₁ c₂ stages h.val s =
        actionMaximum (onlineCappedBackwardQAt (H : ℝ) L c₁ c₂ stages h.val s) ∧
      onlineCappedBackwardValueAt (H : ℝ) L c₁ c₂ stages h.val s =
        onlineCappedBackwardQAt (H : ℝ) L c₁ c₂ stages h.val s
          (onlineCappedGreedyPlanner E L c₁ c₂ history h s) := by
  letI : Nonempty Action := (E h).action_nonempty
  intro stages
  have hlen : h.val < stages.length := by
    simp [stages, onlineCompletedHistoryPlanningStages]
  have hdrop : stages.drop h.val =
      onlineHistoryPlanningStage E history h :: stages.drop (h.val + 1) := by
    rw [List.drop_eq_getElem_cons hlen]
    simp [stages, onlineCompletedHistoryPlanningStages]
  have h1 : onlineCappedBackwardValueAt (H : ℝ) L c₁ c₂ stages h.val s =
      actionMaximum (onlineCappedBackwardQAt (H : ℝ) L c₁ c₂ stages h.val s) := by
    unfold onlineCappedBackwardValueAt onlineCappedBackwardQAt
    rw [hdrop]
    rfl
  refine ⟨h1, h1.trans ?_⟩
  unfold onlineCappedGreedyPlanner actionMaximum
  apply Eq.symm
  exact Classical.choose_spec (p := fun a ↦ onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
    (onlineCompletedHistoryPlanningStages E history) h.val s a =
      Finset.univ.sup' Finset.univ_nonempty
        (onlineCappedBackwardQAt (H : ℝ) L c₁ c₂
          (onlineCompletedHistoryPlanningStages E history) h.val s)) _

/-- Under the burn-in `S³AH³ ≤ K`, the explicit UCBVI rate
`20(√(SAH³K) + S²AH³)(1 + I)` is at most `40√(SAH³K)(1 + I)`. -/
theorem onlineUCBVIRegretRate_le_burnIn (S A H K : ℕ) (δ : ℝ) (hS : 0 < S) (hA : 0 < A)
    (hH : 0 < H) (hK : 0 < K) (hδ : 0 < δ) (hδone : δ < 1)
    (hburn : (S : ℝ) ^ 3 * A * H ^ 3 ≤ K) :
    onlineUCBVIRegretRate S A H K δ ≤
      40 * Real.sqrt ((S : ℝ) * A * H ^ 3 * K) *
        (1 + onlineW1SourceIota S A H K (onlineSourceOptimismDeltaPrime δ S A H K)) := by
  have hdomain := onlineSourceOptimismDeltaPrime_domain δ S A H K hδ hδone.le hS hA hH hK
  set δ' := onlineSourceOptimismDeltaPrime δ S A H K
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hI : 0 ≤ onlineW1SourceIota S A H K δ' := by
    unfold onlineW1SourceIota
    have h1 : 0 ≤ Real.log K / Real.log 2 :=
      div_nonneg (Real.log_nonneg hKr) (Real.log_nonneg (by norm_num))
    have h2 : 0 ≤ Real.log (3 * S * A * H : ℝ) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (S : ℝ) * A * H :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hSr hAr) hHr
      nlinarith
    have h3 : 0 ≤ Real.log (1 / δ') := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hdomain.1]; linarith [hdomain.2]
    positivity
  have hb : (S : ℝ) ^ 2 * A * H ^ 3 ≤ Real.sqrt ((S : ℝ) * A * H ^ 3 * K) := by
    apply Real.le_sqrt_of_sq_le
    have hpos : 0 ≤ (S : ℝ) * A * H ^ 3 := by positivity
    calc ((S : ℝ) ^ 2 * A * H ^ 3) ^ 2 = ((S : ℝ) * A * H ^ 3) * ((S : ℝ) ^ 3 * A * H ^ 3) := by
          ring
      _ ≤ (S : ℝ) * A * H ^ 3 * K := mul_le_mul_of_nonneg_left hburn hpos
  unfold onlineUCBVIRegretRate
  simp only []
  have hx := Real.sqrt_nonneg ((S : ℝ) * A * H ^ 3 * K)
  nlinarith [mul_le_mul_of_nonneg_right hb (by linarith : (0 : ℝ) ≤ 1 + onlineW1SourceIota S A H K δ')]

noncomputable local instance burnInRegretState : MeasurableSpace State := ⊤
noncomputable local instance burnInRegretSample (H K : ℕ) :
  MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

/-- High-probability UCBVI regret after the burn-in: `Regret(K) ≤ 40√(SAH³K)(1 + I)`. -/
theorem onlineUCBVI_actual_regret_burnIn
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ : ℝ) (hδ : 0 < δ) (hδone : δ < 1)
    (hburn : (Fintype.card State : ℝ) ^ 3 * Fintype.card Action * H ^ 3 ≤ K) :
    let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) 4 16
    1 - δ < (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
      {sample : (Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H) |
        (∑ k : Fin K, onlineActualEpisodeRegret H K hH E sample.1 fallback sample.2 k δ' 4 16) ≤
        40 * Real.sqrt ((Fintype.card State : ℝ) * Fintype.card Action * H ^ 3 * K) *
          (1 + onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ')} := by
  intro δ' planner
  have hp := onlineUCBVI_actual_regret_high_probability H K hH hK E ρ fallback δ hδ hδone
  have hS : 0 < Fintype.card State := Fintype.card_pos_iff.mpr ⟨fallback⟩
  have hA : 0 < Fintype.card Action :=
    Fintype.card_pos_iff.mpr (E ⟨0, hH⟩).action_nonempty
  have hrate := onlineUCBVIRegretRate_le_burnIn _ _ H K δ hS hA hH hK hδ hδone hburn
  refine lt_of_lt_of_le hp (measureReal_mono (fun sample hs ↦ ?_) (measure_ne_top _ _))
  exact le_trans hs hrate

end StatisticalRL.OnlineRL
