import Formalization.Online.Regret.MVP.T5.MVPT5ActualBound
import Formalization.Online.Regret.MVP.T5.MVPT8IndependentConfidence
import Formalization.Online.Regret.MVP.T5.MVPT5RadiusAlgebra
import Formalization.Online.Regret.MVP.T5.MVPT5SourceScalars
import Formalization.Online.Regret.MVP.T6.MVPActualVarianceNonnegative

/-! Corrected actual-law MVP T5 source bound, K≥2 branch. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance mvpT5ConfidenceState : MeasurableSpace State := ⊤
noncomputable local instance mvpT5ConfidenceSample (H K : ℕ) : MeasurableSpace
    ((Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) := ⊤

theorem mvpActualT5_source_confidence_K2
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) 4 16
    let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
    1 - 2 * Real.log (K*H) * δp ≤ μ.real
      {sample : (Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H) |
        mvpActualT5 H K hH E sample.1 fallback sample.2 δp 4 16 ≤
          mvpActualW3 H K hH E sample.1 fallback sample.2 δp 4 16 +
          2*(H : ℝ)*mvpVarianceT2 H K hH E sample.1 fallback sample.2 δp 4 16 +
          Real.sqrt ((H : ℝ)^2 * mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δp 4 16 * I) +
          (K : ℝ)*(H : ℝ)^2*I} := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δp
  let q := Real.log (1/δp)
  let planner := onlineMVPCommittedGreedyPlanner hH E fallback q 4 16
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hd := mvp_correctedAllocation_domain_and_log δ (Fintype.card State) (Fintype.card Action) H K
    hδ hδ1 Fintype.card_pos Fintype.card_pos hH (by omega)
  have htail : 0 < δp/2 := by have hdp : 0 < δp := hd.1; positivity
  have htailSmall : δp/2 ≤ 1/100 := by dsimp [δp]; linarith [hd.2.1]
  have hn : 2 ≤ K*H := by nlinarith
  have hp := mvpActualT8_independent_tail_confidence H K hH hn E ρ fallback δp (δp/2) 4 16
    hd.1 hd.2.1 htail htailSmall (by norm_num) (by norm_num)
  have hi := mvpT5_corrected_iota_and_tail_bounds (Fintype.card State) (Fintype.card Action) H K δ
    Fintype.card_pos Fintype.card_pos hH hK hδ hδ1
  have hj := mvpT5_log2_count_le_two_log (K*H) hn
  let good := {sample : (Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H) |
        |mvpVarianceT8 H K hH E sample.1 fallback sample.2 δp 4 16| ≤
          Real.sqrt (32*(H : ℝ)^2*mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δp 4 16 * Real.log (1/(δp/2))) +
            5*(H : ℝ)^2*Real.log (1/(δp/2))}
  let target := {sample : (Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H) |
        mvpActualT5 H K hH E sample.1 fallback sample.2 δp 4 16 ≤
          mvpActualW3 H K hH E sample.1 fallback sample.2 δp 4 16 +
          2*(H : ℝ)*mvpVarianceT2 H K hH E sample.1 fallback sample.2 δp 4 16 +
          Real.sqrt ((H : ℝ)^2*mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δp 4 16 * I) +
          (K : ℝ)*(H : ℝ)^2*I}
  have hsub : good ⊆ target := by
    intro sample hs
    have hv := mvpVarianceT6UCB_nonneg H K hH E sample.1 fallback sample.2 δp 4 16
    have hq : 1 ≤ q := by dsimp [q, δp]; exact hd.2.2
    have hlt : Real.log (1/(δp/2)) ≤ 2*q := by simpa [δp,q,I] using hi.2.2
    have hroot : Real.sqrt (32*(H : ℝ)^2*mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δp 4 16 * Real.log (1/(δp/2))) ≤
        Real.sqrt (64*(H : ℝ)^2*mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δp 4 16*q) := by
      apply Real.sqrt_le_sqrt
      nlinarith [mul_nonneg (sub_nonneg.mpr hlt) (show 0 ≤ (H : ℝ)^2*mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δp 4 16 by positivity)]
    have ht : mvpVarianceT8 H K hH E sample.1 fallback sample.2 δp 4 16 ≤
        Real.sqrt (64*(H : ℝ)^2*mvpVarianceT6UCB H K hH E sample.1 fallback sample.2 δp 4 16*q) + 10*(H : ℝ)^2*q := by
      have := le_abs_self (mvpVarianceT8 H K hH E sample.1 fallback sample.2 δp 4 16)
      dsimp [good] at hs
      nlinarith [mul_nonneg (sq_nonneg (H : ℝ)) (sub_nonneg.mpr hlt)]
    have hdet := mvpActualT5_le_W3_T8_T2 H K hH E sample.1 fallback sample.2 δp 4 16 hd.1 (le_trans hd.2.1 (by norm_num)) (by norm_num) (by norm_num)
    exact mvpT5_radius_absorption H K _ q I _ _ _ _ (by positivity) (by exact_mod_cast (show 1 ≤ K by omega)) hv hq
      (by simpa [δp,q,I] using hi.1) (by simpa [δp,q,I] using hi.2.1) hdet ht
  have hm := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
  change μ.real good ≤ μ.real target at hm
  have hp' : 1 - (Nat.log2 (K*H) : ℝ)*δp ≤ μ.real good := by
    change 1 - 2*(Nat.log2 (K*H) : ℝ)*(δp/2) ≤ μ.real good at hp
    linarith
  have hj' := mul_le_mul_of_nonneg_right hj (show 0 ≤ δp from le_of_lt hd.1)
  push_cast at hj'
  change 1 - 2*Real.log (K*H)*δp ≤ μ.real target
  linarith
end StatisticalRL.OnlineRL
