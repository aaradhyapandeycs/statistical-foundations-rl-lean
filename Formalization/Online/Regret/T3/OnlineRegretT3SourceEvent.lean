import Formalization.Online.Regret.T3.OnlineRegretT3PublicSum
import Formalization.Online.Regret.T3.OnlineRegretT3VarianceTransport
import Formalization.Online.Regret.T3.OnlineRegretT3SourceBound
import Formalization.Online.SourceOptimism.SourceOptimismAllocation
import Formalization.Online.Regret.Algebra.OnlineVarianceRadiusAlgebra
import Formalization.Online.Regret.T3.T3Definitions

/-! Source-allocated T₃ event under the actual sequential law, with both printed T₃ inequalities. This is not the full regret theorem. -/

namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction}
  [Fintype State] [Fintype Action]
noncomputable local instance t3EventStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance t3EventStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance t3EventActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Source-allocated T₃ bound for the actual episode array. It uses the exact
printed δ′ denominator, actual chosen rows, and the same sequential law as the
other source events. The strict K≥2 domain ensures the Freedman peeling index
is positive. -/
theorem onlineSourceAllocated_actualT3_bound
    (H K : ℕ) (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ c₁ c₂ : ℝ)
    (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    let δ' := onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    1 - 2 * (Real.log ((K : ℝ) * H) / Real.log 2) * δ' ≤
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        (onlineActualT3SourceBoundEvent H K hH E fallback δ' c₁ c₂) := by
  classical
  let S := Fintype.card State
  let A := Fintype.card Action
  let δ' := onlineSourceOptimismDeltaPrime δ S A H K
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  let ℱ := onlineT3ActualPrefixFiltration H K hH fallback planner
  let X := onlineT3PaddedY H K hH E ρ fallback planner (Real.log (1 / δ')) c₁ c₂
  let N := K * H
  have hKpos : 0 < K := by omega
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  have hN : 2 ≤ N := by
    dsimp [N]
    exact hK.trans (Nat.le_mul_of_pos_right K hH)
  have hdomain := onlineSourceOptimismDeltaPrime_domain δ S A H K hδ hδone
    (Fintype.card_pos) (Fintype.card_pos) hH hKpos
  have hδpos : 0 < δ' := by simpa [δ'] using hdomain.1
  have hδsmall : δ' ≤ 1 / 100 := by simpa [δ'] using hdomain.2
  have hSreal : (1 : ℝ) ≤ (S : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card State))
  have hAreal : (1 : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card Action))
  have hHreal : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hH)
  have hKreal : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hKpos)
  have hNreal : 0 < (N : ℝ) := by dsimp [N]; positivity
  have hdenLower : 100 * (N : ℝ) ≤
      100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2 := by
    calc
      100 * (N : ℝ) = 100 * (H : ℝ) * (K : ℝ) := by
        dsimp [N]
        push_cast
        ring
      _ ≤ 100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2 := by
        have hsSq : (1 : ℝ) ≤ (S : ℝ)^2 := by nlinarith [hSreal]
        have haSq : (1 : ℝ) ≤ (A : ℝ)^2 := by nlinarith [hAreal]
        have hhSq : (1 : ℝ) ≤ (H : ℝ)^2 := by nlinarith [hHreal]
        have hkSq : (1 : ℝ) ≤ (K : ℝ)^2 := by nlinarith [hKreal]
        have hHsq : (H : ℝ) ≤ (H : ℝ)^2 := by nlinarith [hHreal]
        have hKsq : (K : ℝ) ≤ (K : ℝ)^2 := by nlinarith [hKreal]
        have hHK₁ : (H : ℝ) * (K : ℝ) ≤ (H : ℝ)^2 * (K : ℝ) :=
          mul_le_mul_of_nonneg_right hHsq (by positivity)
        have hHK₂ : (H : ℝ)^2 * (K : ℝ) ≤ (H : ℝ)^2 * (K : ℝ)^2 :=
          mul_le_mul_of_nonneg_left hKsq (sq_nonneg (H : ℝ))
        have hSstep : (H : ℝ)^2 * (K : ℝ)^2 ≤
            (S : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2 := by
          have hh := mul_le_mul_of_nonneg_right hsSq
            (mul_nonneg (sq_nonneg (H : ℝ)) (sq_nonneg (K : ℝ)))
          calc
            (H : ℝ)^2 * (K : ℝ)^2 = 1 * ((H : ℝ)^2 * (K : ℝ)^2) := by ring
            _ ≤ (S : ℝ)^2 * ((H : ℝ)^2 * (K : ℝ)^2) := hh
            _ = (S : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2 := by ring
        have hAstep : (S : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2 ≤
            (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2 := by
          have hh := mul_le_mul_of_nonneg_right haSq
            (mul_nonneg (sq_nonneg (S : ℝ))
              (mul_nonneg (sq_nonneg (H : ℝ)) (sq_nonneg (K : ℝ))))
          nlinarith [hh]
        calc
          100 * (H : ℝ) * (K : ℝ) = 100 * ((H : ℝ) * (K : ℝ)) := by ring
          _ ≤ 100 * ((H : ℝ)^2 * (K : ℝ)^2) := by
            exact mul_le_mul_of_nonneg_left (hHK₁.trans hHK₂) (by norm_num)
          _ ≤ 100 * ((S : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2) :=
            mul_le_mul_of_nonneg_left hSstep (by norm_num)
          _ ≤ 100 * ((S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2) :=
            mul_le_mul_of_nonneg_left hAstep (by norm_num)
          _ = 100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2 := by ring
  have hδbound : δ' ≤ 1 / (100 * (N : ℝ)) := by
    have hDpos : 0 < 100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2 := by positivity
    have hNden : 0 < 100 * (N : ℝ) := by positivity
    have hcross : δ * (100 * (N : ℝ)) ≤
        100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2 := by
      have hleft := mul_le_mul_of_nonneg_right hδone (by positivity : 0 ≤ 100 * (N : ℝ))
      have hdenLower' : 1 * (100 * (N : ℝ)) ≤
          100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2 := by
        simpa only [one_mul] using hdenLower
      exact hleft.trans hdenLower'
    dsimp [δ', onlineSourceOptimismDeltaPrime]
    rw [div_le_div_iff₀ hDpos hNden]
    simpa using hcross
  have hj : Nat.log2 N ≤ N := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_le_self 2 N
  have hbranch : 2 * (Nat.log2 N : ℝ) * δ' < 1 := by
    have hjreal : (Nat.log2 N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
    have hmul₁ := mul_le_mul_of_nonneg_right hjreal (le_of_lt hδpos)
    have hmul₂ := mul_le_mul_of_nonneg_left hδbound (by positivity : 0 ≤ 2 * (N : ℝ))
    have hratio : 2 * (N : ℝ) * (1 / (100 * (N : ℝ))) < 1 := by
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNreal
      field_simp [hNne]
      norm_num
    nlinarith
  have hjlog : (Nat.log2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    simpa [Real.logb] using (Real.log2_le_logb N)
  have hL : 2 ≤ Real.log (1 / δ') :=
    onlineT3_sourceLog_ge_two δ' hδpos hδsmall
  have hfirst := onlineT3_source_first_radius_probability H K (Nat.log2 N) hH hN
    E ρ fallback planner c₁ c₂ δ' hc₁ hc₂ hδpos hδsmall rfl hbranch
  letI : MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) :=
    FiniteDistribution.empiricalRowStateMeasurable
  have hvar := onlineT3PredictableSecondMomentSum_eq_actualT6UCB_ae
    H K hH E ρ fallback δ' c₁ c₂
  have hsub :
      onlineFreedmanSourceRadiusSet μ ℱ X (K * H) (H : ℝ) (Real.log (1 / δ')) ≤ᵐ[μ]
        onlineActualT3SourceBoundEvent H K hH E fallback δ' c₁ c₂ := by
    filter_upwards [hvar] with sample hv hrad
    unfold onlineActualT3SourceBoundEvent
    have hsum := onlineT3PaddedY_sum_eq_publicT3 H K hH E ρ fallback sample
      δ' c₁ c₂
    have hradius :
        |incrementSum X (K * H) sample| ≤
          Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2
              δ' c₁ c₂ * Real.log (1 / δ')) +
            5 * (H : ℝ) * Real.log (1 / δ') := by
      change |incrementSum X (K * H) sample| ≤
        Real.sqrt (8 * predictableSecondMomentSum μ ℱ X (K * H) sample * Real.log (1 / δ')) +
          5 * (H : ℝ) * Real.log (1 / δ') at hrad
      rw [hv] at hrad
      exact hrad
    have hT6 := onlineActualT6UCB_le_policy_difference H K hH E sample.1 fallback sample.2
      δ' c₁ c₂
    have hp : 0 ≤ onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ := by
      unfold onlineActualT6Policy
      apply Finset.sum_nonneg
      intro h hh
      apply Finset.sum_nonneg
      intro k hk
      exact FiniteDistribution.variance_nonneg _ _
    have hd : 0 ≤ onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ := by
      unfold onlineActualT6Difference
      apply Finset.sum_nonneg
      intro h hh
      apply Finset.sum_nonneg
      intro k hk
      exact FiniteDistribution.expectation_nonneg _ (fun _ => sq_nonneg _)
    have hroot :
        Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
          Real.log (1 / δ')) ≤
        4 * Real.sqrt (onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
          Real.log (1 / δ')) +
        4 * Real.sqrt (onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
          Real.log (1 / δ')) := by
      exact onlineVarianceRadius_le_policy_difference
        (onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂)
        (onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂)
        (onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂)
        (Real.log (1 / δ'))
        (Finset.sum_nonneg (fun h hh => Finset.sum_nonneg (fun k hk =>
          FiniteDistribution.variance_nonneg _ _)))
        hp hd (le_trans (by norm_num) hL) hT6
    have hsourceFirst :
        |∑ k : Fin K,
          (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).2.2.1| ≤
          Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2
            δ' c₁ c₂ * Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ') := by
      calc
        _ = |incrementSum X (K * H) sample| := by rw [← hsum]; rfl
        _ ≤ _ := hradius
    have hsourceSecond :
        Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
          Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ') ≤
        4 * Real.sqrt (onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
          Real.log (1 / δ')) +
        4 * Real.sqrt (onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
          Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ') := by
      have h := add_le_add_right hroot
        (5 * (H : ℝ) * Real.log (1 / δ'))
      calc
        _ = (5 * (H : ℝ) * Real.log (1 / δ')) +
            Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
              Real.log (1 / δ')) := by ring
        _ ≤ _ := h
        _ = _ := by ring
    exact ⟨hsourceFirst, hsourceSecond⟩
  have hprob := measure_mono_ae hsub
  have hfirst' := hfirst
  have hreal := ENNReal.toReal_mono (measure_ne_top μ _) hprob
  have hprob' : 1 - 2 * (Nat.log2 N : ℝ) * δ' ≤
      μ.real (onlineActualT3SourceBoundEvent H K hH E fallback δ' c₁ c₂) :=
    hfirst'.trans hreal
  have hconf := mul_le_mul_of_nonneg_right hjlog (le_of_lt hδpos)
  have hmargin :
      1 - 2 * (Real.log (N : ℝ) / Real.log 2) * δ' ≤
        1 - 2 * (Nat.log2 N : ℝ) * δ' := by
    linarith
  have hcast : (N : ℝ) = (K : ℝ) * (H : ℝ) := by
    dsimp [N]
    exact_mod_cast (Nat.cast_mul K H)
  rw [hcast] at hmargin
  exact hmargin.trans hprob'
end StatisticalRL.OnlineRL
