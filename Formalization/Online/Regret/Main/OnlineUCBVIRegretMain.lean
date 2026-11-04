import Formalization.Online.Regret.Main.OnlineUCBVIMainHelpers

/-! Corrected actual-law finite-horizon UCBVI regret bound, using fixed universal constants 4 and 16, finite zero-count completion, and fixed ties. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
open MeasureTheory ProbabilityTheory
universe uState uAction
variable {State : Type uState} {Action : Type uAction} [Fintype State] [Fintype Action]
noncomputable local instance mainRegretState : MeasurableSpace State := ⊤
noncomputable local instance mainRegretSample (H K : ℕ) :
  MeasurableSpace ((Fin K → State) × OnlineOutcomePath.{uState, 0} State (K * H)) := ⊤

/-- On the actual independent reset-and-transition experiment, corrected UCBVI
has the explicit high-probability finite-horizon regret rate. The K=1 case
is handled directly rather than by the vanishing source iota. -/
theorem onlineUCBVI_actual_regret_high_probability
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (δ : ℝ) (hδ : 0 < δ) (hδone : δ < 1) :
    let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) 4 16
    1 - δ < (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
      (onlineUCBVIRegretRateEvent H K hH E fallback δ) := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let S := Fintype.card State
  let A := Fintype.card Action
  let δ' := onlineSourceOptimismDeltaPrime δ S A H K
  let I := onlineW1SourceIota S A H K δ'
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) 4 16
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hS : 0 < S := Fintype.card_pos
  have hA : 0 < A := Fintype.card_pos
  have hs : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have ha : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hh : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hdomain := onlineSourceOptimismDeltaPrime_domain δ S A H K hδ (le_of_lt hδone) hS hA hH hK
  change 1 - δ < μ.real (onlineUCBVIRegretRateEvent H K hH E fallback δ)
  by_cases hKone : K = 1
  · have hall : onlineUCBVIRegretRateEvent H K hH E fallback δ = Set.univ := by
      ext sample
      simp only [Set.mem_univ, iff_true]
      have hr := onlineActualRegret_sum_le_KH H K hH E sample.1 fallback sample.2 δ' 4 16
      have hb := onlineMain_one_scalar (S : ℝ) (A : ℝ) (H : ℝ) hs ha hh
      have hIzero : I = 0 := by simp [I, onlineW1SourceIota, hKone]
      change (∑ k : Fin K, onlineActualEpisodeRegret H K hH E sample.1 fallback sample.2 k δ' 4 16) ≤
        20 * (Real.sqrt ((S : ℝ) * A * H^3 * K) + (S : ℝ)^2 * A * H^3) * (1 + I)
      simp only [hKone, Nat.cast_one, mul_one, hIzero, add_zero] at hr hb ⊢
      exact (by simpa only [one_mul] using hr : _ ≤ (H : ℝ)).trans hb
    rw [hall, probReal_univ]
    linarith
  · have hK2 : 2 ≤ K := by omega
    have hi := onlineT56_source_iota_large S A H K δ' hS hA hH hK2 hdomain.1 hdomain.2
    have hL : 0 ≤ Real.log (1 / δ') :=
      (onlineSmallConfidence_log_ge_one δ' hdomain.1 hdomain.2).trans' (by norm_num)
    have hI : 0 ≤ I := by dsimp [I]; nlinarith
    by_cases hsmall : (K : ℝ) ≤ (S : ℝ) * A * H^2 * I
    · have hall : onlineUCBVIRegretRateEvent H K hH E fallback δ = Set.univ := by
        ext sample
        simp only [Set.mem_univ, iff_true]
        have hr := onlineActualRegret_sum_le_KH H K hH E sample.1 fallback sample.2 δ' 4 16
        have hb := onlineMain_small_scalar (S : ℝ) (A : ℝ) (H : ℝ) (K : ℝ) I
          hs ha hh (by positivity) hI hsmall
        change (∑ k : Fin K, onlineActualEpisodeRegret H K hH E sample.1 fallback sample.2 k δ' 4 16) ≤
          20 * (Real.sqrt ((S : ℝ) * A * H^3 * K) + (S : ℝ)^2 * A * H^3) * (1 + I)
        exact hr.trans hb
      rw [hall, probReal_univ]
      linarith
    · have hlarge : (S : ℝ) * A * H^2 * I ≤ K := le_of_lt (lt_of_not_ge hsmall)
      let T0 := onlineActualT0OptimisticUniformEvent H K hH E fallback δ' 4 16
      let B := onlineActualT56JointEvent H K hH E fallback δ' 4 16 ∩
        onlineActualT56SimplifiedEvent H K hH E fallback δ' 4 16
      have hp0 := onlineT0_optimisticUniform_actual_confidence H K hH hK2 E ρ fallback δ' 4 16
        hdomain.1 hdomain.2 (by norm_num) (by norm_num)
      have hpB := onlineSourceT56Simplified_actual_confidence_fixed_constants H K hH hK2 E ρ fallback δ
        hδ (le_of_lt hδone) hlarge
      have hp := onlineTwoEvent_confidence_strict μ T0 B
        (9 * (S : ℝ)^2 * A * H^2 * K * δ') (30 * (S : ℝ)^2 * A * H^2 * K * δ')
        (le_of_lt hp0) hpB
      have hsub : T0 ∩ B ⊆ onlineUCBVIRegretRateEvent H K hH E fallback δ := by
        intro sample hsamp
        have hr := onlineActualRegret_sum_le_sourceT0_of_event H K hH E fallback sample δ' 4 16 hsamp.1
        have hscalar := onlineUCBVI_actual_T0_closure_of_component_bounds H K hH hK2 E fallback sample δ'
          hdomain.1 hdomain.2 hsamp.2.2.1 hsamp.2.2.2 hsamp.2.1.2.2
        have hx : 0 ≤ Real.sqrt ((S : ℝ) * A * H^3 * K) := Real.sqrt_nonneg _
        have hb : 0 ≤ (S : ℝ)^2 * A * H^3 := by positivity
        have hscalar' : onlineActualT0SourceUpper H K hH E fallback sample δ' 4 16 ≤
            20 * Real.sqrt ((S : ℝ) * A * H^3 * K) * I + 15 * ((S : ℝ)^2 * A * H^3) * I := by
          simpa only [mul_assoc] using hscalar
        have hrate := onlineMain_large_scalar _ _ I _ hx hb hI hscalar'
        change (∑ k : Fin K, onlineActualEpisodeRegret H K hH E sample.1 fallback sample.2 k δ' 4 16) ≤
          20 * (Real.sqrt ((S : ℝ) * A * H^3 * K) + (S : ℝ)^2 * A * H^3) * (1 + I)
        exact hr.trans hrate
      have hm := measureReal_mono (μ := μ) hsub (by simp)
      have hcost := onlineMain_allocated_failure_le_delta S A H K δ hS hA hH hK hδ
      change 39 * (S : ℝ)^2 * A * H^2 * K * δ' ≤ δ at hcost
      nlinarith only [hp, hm, hcost]
end StatisticalRL.OnlineRL
