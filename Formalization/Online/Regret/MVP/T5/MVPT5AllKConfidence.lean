import Formalization.Online.Regret.MVP.T5.MVPT5Confidence
import Formalization.Online.Regret.MVP.T5.MVPT5K1
import Formalization.Online.Regret.MVP.T5.MVPT8IndependentConfidence
import Formalization.Online.Regret.MVP.T5.MVPT5RadiusAlgebra
import Formalization.Online.Regret.MVP.T5.MVPT5SourceScalars
import Formalization.Online.Regret.MVP.T6.MVPActualVarianceNonnegative

/-! Corrected actual-law MVP T5 source bound, K≥2 branch. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance mvpT5AllKState : MeasurableSpace State := ⊤
noncomputable local instance mvpT5AllKSample (H K : ℕ) : MeasurableSpace
    ((Fin K → State) × OnlineOutcomePath.{uState,0} State (K*H)) := ⊤

theorem mvpActualT5_source_confidence
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K) (E : Fin H → EnvironmentStage State Action)
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
  by_cases hk : 2 ≤ K
  · exact mvpActualT5_source_confidence_K2 H K hH hk E ρ fallback δ hδ hδ1
  · have hK1 : K = 1 := by omega
    subst K
    letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
    letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
    let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H 1
    let I := onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H 1 δp
    let planner := onlineMVPCommittedGreedyPlanner hH E fallback (Real.log (1/δp)) 4 16
    let μ := (onlineSequentialEpisodeLaw H 1 hH E ρ fallback planner (1*H)).rowMeasure
    haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
    have hd := mvp_correctedAllocation_domain_and_log δ (Fintype.card State) (Fintype.card Action) H 1
      hδ hδ1 Fintype.card_pos Fintype.card_pos hH (by norm_num)
    have hq : 0 ≤ Real.log (1/δp) := by dsimp [δp]; linarith [hd.2.2]
    let target := {sample : (Fin 1 → State) × OnlineOutcomePath.{uState,0} State (1*H) |
      mvpActualT5 H 1 hH E sample.1 fallback sample.2 δp 4 16 ≤
        mvpActualW3 H 1 hH E sample.1 fallback sample.2 δp 4 16 +
        2*(H : ℝ)*mvpVarianceT2 H 1 hH E sample.1 fallback sample.2 δp 4 16 +
        Real.sqrt ((H : ℝ)^2*mvpVarianceT6UCB H 1 hH E sample.1 fallback sample.2 δp 4 16 * I) +
        (1 : ℝ)*(H : ℝ)^2*I}
    have hi : I = 0 := by simp [I, onlineW1SourceIota]
    have ht : target = Set.univ := by
      apply Set.eq_univ_of_forall
      intro sample
      have hz := mvp_actualT5_W3_one_episode_zero H hH E sample.1 fallback sample.2 δp 4 16
      have hn := mvpVarianceT2_nonneg H 1 hH E sample.1 fallback sample.2 δp 4 16 hq (by norm_num) (by norm_num)
      dsimp [target]
      rw [hz.1, hz.2, hi]
      simp
      positivity
    have hlog : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ H by omega))
    have hbound : 1 - 2*Real.log (H : ℝ)*δp ≤ μ.real target := by
      rw [ht]
      simp only [measureReal_univ_eq_one]
      nlinarith [mul_nonneg hlog (show 0 ≤ δp from le_of_lt hd.1)]
    simpa only [Nat.cast_mul, Nat.cast_one, one_mul, δp, I, planner, μ, target] using hbound
end StatisticalRL.OnlineRL
