import Formalization.Online.Regret.MVP.T34.MVPActualT3Confidence
import Formalization.Online.Regret.MVP.T34.MVPActualT4Confidence
import Formalization.Online.Regret.MVP.T34.MVPJointLogScalars
import Formalization.Online.Regret.MVP.T34.MVPJointRadiusScalars
import Formalization.Online.Regret.MVP.T2.MVPT2ActualSource
import Formalization.Probability.OnlineT234ConfidenceAlgebra
import Formalization.Online.Regret.MVP.T6.MVPActualVarianceNonnegative

/-! Joint actual-law MVP T2/T3/T4 confidence bound for the fixed retained-table planner. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance mvpJointState : MeasurableSpace State := ⊤
noncomputable local instance mvpJointSample (H K : ℕ) : MeasurableSpace
    ((Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) := ⊤

noncomputable def mvpActualT234Event
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (fallback : State) (δp I : ℝ) : Set ((Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) :=
  {sample |
    mvpVarianceT2 H K hH E sample.1 fallback sample.2 δp 4 16 ≤
      (1/2 : ℝ)*Real.sqrt ((Fintype.card State : ℝ)*Fintype.card Action*H*
        mvpActualT5 H K hH E sample.1 fallback sample.2 δp 4 16*I) +
        (1/2 : ℝ)*(Fintype.card State : ℝ)*Fintype.card Action*(H : ℝ)^2*I ∧
    |mvpActualT3 H K hH E sample.1 fallback sample.2 δp 4 16| ≤
      Real.sqrt (mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δp 4 16*I) + (H : ℝ)*I ∧
    |mvpActualT4 H K hH E sample.1 fallback sample.2 (Real.log (1/δp)) 4 16| ≤
      Real.sqrt ((K : ℝ)*(H : ℝ)^2*I)}

theorem mvpActualT234_source_confidence_K2
    (H K : ℕ) (hH : 0<H) (hK : 2≤K) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) :
    let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) 4 16
    1 - 4*(Real.log K/Real.log 2)*δp <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        (mvpActualT234Event H K hH E fallback δp I) := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp
  let q := Real.log (1/δp)
  let B := Real.log K/Real.log 2
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback q 4 16
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hd := mvp_correctedAllocation_domain_and_log δ (Fintype.card State) (Fintype.card Action) H K
    hδ hδ1 Fintype.card_pos Fintype.card_pos hH (by omega)
  have ht := mvpJoint_corrected_tail_logs (Fintype.card State) (Fintype.card Action) H K δ
    Fintype.card_pos Fintype.card_pos hH hK hδ hδ1
  have htail : 0 < δp/((H : ℝ)+1) := by simpa [δp] using ht.1
  have htailSmall : δp/((H : ℝ)+1) ≤ 1/100 := by simpa [δp] using ht.2.1
  have hhalf : 0 < δp/2 := by have h : 0<δp := hd.1; positivity
  have hhalf1 : δp/2 < 1 := by dsimp [δp]; linarith [hd.2.1]
  have hq : 0 ≤ q := by dsimp [q,δp]; linarith [hd.2.2]
  have hq3 : Real.log (1/(δp/((H : ℝ)+1))) ≤ 2*q := by simpa [δp,q,I] using ht.2.2.1
  have hq4 : Real.log (1/(δp/2)) ≤ 2*q := mvpJoint_halfTail_log δp hd.1 hd.2.2
  have hi16 : 16*q ≤ I := by simpa [δp,q,I] using ht.2.2.2.1
  have hi10 : 10*q ≤ I := by simpa [δp,q,I] using ht.2.2.2.2
  have hn : 2 ≤ K*H := by nlinarith
  let good3 : Set ((Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) :=
    {sample | |mvpActualT3 H K hH E sample.1 fallback sample.2 δp 4 16| ≤
      Real.sqrt (8*mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δp 4 16 * Real.log (1/(δp/((H : ℝ)+1)))) +
      5*(H : ℝ)*Real.log (1/(δp/((H : ℝ)+1)))}
  let good4 : Set ((Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) :=
    {sample | |mvpActualT4 H K hH E sample.1 fallback sample.2 q 4 16| ≤
      Real.sqrt (2*(K : ℝ)*(H : ℝ)^2*Real.log (1/(δp/2)))}
  have h3 : 1 - 2*(Nat.log2 (K*H) : ℝ)*(δp/((H : ℝ)+1)) ≤ μ.real good3 := by
    simpa [μ, planner, q, good3] using mvpActualT3_independent_tail_confidence H K hH hn E ρ fallback δp
      (δp/((H : ℝ)+1)) 4 16 hd.1 hd.2.1 htail htailSmall (by norm_num) (by norm_num)
  have h4 : 1 - 2*(δp/2) < μ.real good4 := by
    simpa [μ, planner, q, good4] using mvpActualT4_source_confidence_strict H K hH (by omega) E ρ fallback
      q 4 16 (δp/2) hhalf hhalf1
  have hinter := onlineTwoEvent_confidence_strict μ good3 good4
    (2*(Nat.log2 (K*H) : ℝ)*(δp/((H : ℝ)+1))) (2*(δp/2)) h3 h4
  have hsub : good3 ∩ good4 ⊆ mvpActualT234Event H K hH E fallback δp I := by
    intro sample hs
    have hv := mvpVarianceT6UCB_nonneg H K hH E sample.1 fallback sample.2 δp 4 16
    have hq3non : 0 ≤ Real.log (1/(δp/((H : ℝ)+1))) := by
      exact le_trans (by norm_num) (onlineT3_sourceLog_ge_two _ htail htailSmall)
    have h3bound := mvpJoint_T3_radius_absorb _ H q _ I hv (by positivity) hq hq3non hq3 hi16 hi10
    have h4bound := mvpJoint_T4_radius_absorb K H q _ I (by positivity) (by positivity) hq4 (by nlinarith)
    have h2 := mvpActualT2_le_sourceBound_fixed H K hH hK E sample.1 fallback sample.2 δ hδ hδ1
    refine ⟨?_, ?_, ?_⟩
    · simpa [δp,I] using h2
    · exact le_trans hs.1 h3bound
    · exact le_trans hs.2 h4bound
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have hj := mvpJoint_log2_KH_le_Hplus_log2K K H hK hH
  have hB : 1 ≤ B := by
    dsimp [B]; apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ)<2))).2
    simpa using Real.log_le_log (by norm_num : (0 : ℝ)<2) (show (2 : ℝ)≤K by exact_mod_cast hK)
  have hdiv : (Nat.log2 (K*H) : ℝ)/((H : ℝ)+1) ≤ B := by
    apply (div_le_iff₀ (by positivity : 0<(H : ℝ)+1)).2
    simpa [B, mul_comm] using hj
  have hbudget : 2*(Nat.log2 (K*H) : ℝ)*(δp/((H : ℝ)+1)) + 2*(δp/2) ≤ 4*B*δp := by
    have h := mul_le_mul_of_nonneg_right hdiv (show 0 ≤ δp from le_of_lt hd.1)
    have hb := mul_nonneg (sub_nonneg.mpr hB) (show 0 ≤ δp from le_of_lt hd.1)
    have heq : (Nat.log2 (K*H) : ℝ)*(δp/((H : ℝ)+1)) =
        ((Nat.log2 (K*H) : ℝ)/((H : ℝ)+1))*δp := by ring
    nlinarith [heq]
  change 1 - 4*B*δp < μ.real (mvpActualT234Event H K hH E fallback δp I)
  linarith
end StatisticalRL.OnlineRL
