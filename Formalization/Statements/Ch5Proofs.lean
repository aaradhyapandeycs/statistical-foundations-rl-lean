import Formalization.Online.Regret.MVP.OnlineMVPArbitraryHistory
import Formalization.Online.Regret.MVP.MVPProfileCardinality
import Formalization.Online.Regret.MVP.MVPActualProfiles
import Formalization.Probability.SquaredVarianceBounds
import Formalization.Online.Regret.Main.OnlineUCBVIRegretMain
import Formalization.Online.Regret.Joint.OnlineT56SourceConfidence
import Formalization.Online.Regret.Joint.OnlineT234Joint
import Formalization.Online.Regret.PolicyVariance.FinitePolicyVarianceSource
import Formalization.Statements.Ch5
import Formalization.Online.Regret.Counts.OnlineReciprocalSource
import Formalization.Online.SourceOptimism.SourceOptimismAllocation
import Formalization.Online.Regret.NonnegativeTelescope
import Formalization.Online.Regret.W1.OnlineW1RestrictedSourceBudget
import Formalization.Online.Regret.Joint.OnlineW123Final

namespace StatisticalRL.Statements
open StatisticalRL.OnlineRL

theorem Lemma5_5_corrected_holds : Lemma5_5_corrected := by
  intro State Action instS instA H K hH hK E ρ δ c₁ c₂ hδ hδone hc₁ hc₂
  simpa only [onlineSourceOptimismDeltaPrime, onlineHistoryAllStageTrajectoryOptimism] using
    onlineSourceAllocated_allStageTrajectoryOptimism_strict H K hH hK E ρ (Classical.choice (E ⟨0, hH⟩).state_nonempty) δ c₁ c₂
      hδ hδone hc₁ hc₂

/-- Consume the nonnegative-parameter telescope for the printed log scale. -/
theorem Lemma5_6_corrected_holds : Lemma5_6_corrected := by
  intro State Action instS instA instNS instNA H hH stage state action δ' c₁ c₂
    hδ' hδone hc₁ hc₂ hgreedy
  have hratio : (1 : ℝ) ≤ 1 / δ' :=
    (le_div_iff₀ hδ').2 (by simpa using hδone)
  have hL : 0 ≤ Real.log (1 / δ') := Real.log_nonneg hratio
  have h := onlineCappedEpisode_realized_telescope_nonnegative H stage state action
    (Real.log (1 / δ')) c₁ c₂ hL hc₁ hc₂ (fun _ => inferInstance) hgreedy
  simpa only [onlineCappedEpisodeValueAlongPath, List.drop_zero,
    onlineCappedEpisodeTelescopeSummand] using h

/-- Derive the printed W₁ confidence from the stronger proved 6SAHK budget. -/
theorem Lemma5_7_W1_K2_corrected_holds : Lemma5_7_W1_K2_corrected := by
  intro State Action instS instA H K hH hK E ρ δ c₁ c₂ hδ hδone hc₁ hc₂
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let S : ℝ := Fintype.card State
  let A : ℝ := Fintype.card Action
  let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  have hS : 1 ≤ S := by
    change 1 ≤ (Fintype.card State : ℝ)
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos (α := State)))
  have hd : 0 < δ' := by
    dsimp [δ', onlineSourceOptimismDeltaPrime]
    positivity
  have hf : 6 * S ≤ 12 * S^2 := by nlinarith
  have hb := mul_le_mul_of_nonneg_right hf (show 0 ≤ A * H * K * δ' by positivity)
  have hc : 1 - 12 * S^2 * A * H * K * δ' ≤ 1 - 6 * S * A * H * K * δ' := by
    nlinarith
  have hp := onlineSourceAllocated_actualW1RestrictedIota_strict H K hH hK E ρ
    (Classical.choice (E ⟨0, hH⟩).state_nonempty) δ c₁ c₂ hδ hδone hc₁ hc₂
  have hp' := lt_of_le_of_lt hc hp
  simpa only [S, A, δ', onlineSourceOptimismDeltaPrime,
    onlineActualW1RestrictedIotaEvent, onlineW1SourceIota] using hp'

/-- Consume the joint same-experiment export; expand all three source bounds. -/
theorem Lemma5_7_K2_corrected_holds : Lemma5_7_K2_corrected := by
  intro State Action instS instA H K hH hK E ρ δ c₁ c₂ hδ hδone hc₁ hc₂
  simpa only [onlineSourceOptimismDeltaPrime, onlineActualW123RestrictedEvent,
    Set.inter_def, Set.mem_setOf_eq, onlineActualW1RestrictedIotaEvent,
    onlineActualW2RestrictedIotaEvent, onlineActualW3RestrictedIotaEvent,
    onlineW1SourceIota] using
    onlineSourceAllocated_actualW123Restricted_strict H K hH hK E ρ
      (Classical.choice (E ⟨0, hH⟩).state_nonempty) δ c₁ c₂ hδ hδone hc₁ hc₂


/-- The actual-path count identity reduces Lemma 5.3 to its deterministic
finite-row rank budget. -/
theorem Lemma5_3_holds : Lemma5_3 := by
  intro State Action instS instA H K hH hK E initial fallback planner path
  dsimp only [Lemma5_3]
  rw [Finset.sum_comm]
  simpa only [onlineReciprocalMaxOneCount, one_div] using
    onlineSequential_maxOne_reciprocal_count_budget H K hH hK E initial fallback planner path


/-- Average the stronger pointwise-in-initial-state export under the source
initial distribution. -/

theorem Lemma5_4_holds : Lemma5_4 := by
  intro State Action instS instA H _hH E ρ π
  dsimp only
  apply ρ.expectation_le_const
  intro s
  exact finitePolicy_expected_cumulative_variance_le_horizon_sq H E π s


/-- Instantiate the applying joint export at the exact printed iota and
expand all three source terms and both T3 inequalities. -/
theorem Lemma5_8_K2_corrected_holds : Lemma5_8_K2_corrected := by
  intro State Action instS instA H K hH hK E ρ δ c₁ c₂ hδ hδone hc₁ hc₂
  dsimp only
  intro hI
  have hp := onlineSourceAllocated_actualT234_K2_strict H K hH hK E ρ
    (Classical.choice (E ⟨0, hH⟩).state_nonempty) δ c₁ c₂
    (onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K
      (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K))
    hδ hδone hc₁ hc₂ hI
  simpa only [onlineSourceOptimismDeltaPrime, onlineW1SourceIota,
    onlineActualT234SourceEvent, onlineActualT3SourceBoundEvent,
    onlineActualT2, Set.mem_setOf_eq, Set.setOf_app_iff, and_assoc] using hp

/-- Apply the unconditional actual-law export, weaken its strict confidence,
and project its stronger joint event onto the printed simplified event. -/
theorem Lemma5_9_K2_corrected_holds : Lemma5_9_K2_corrected := by
  intro State Action instS instA H K hH hK E ρ δ hδ hδone
  let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
  let δ' := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) 4 16
  let μ := (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure
  have hp := onlineSourceAllocated_T3_T56_simplified_actual_confidence
    H K hH hK E ρ fallback δ hδ hδone.le
  dsimp only
  refine ⟨?_, ?_⟩
  · simpa only [fallback, onlineSourceOptimismDeltaPrime, onlineW1SourceIota,
      onlineActualT56JointEvent, onlineActualT0SourceUpper] using hp.1.le
  · intro hlarge
    have hlarge' : (Fintype.card State : ℝ) * Fintype.card Action * H^2 *
        onlineW1SourceIota (Fintype.card State) (Fintype.card Action) H K δ' ≤ K := by
      simpa only [δ', onlineSourceOptimismDeltaPrime, onlineW1SourceIota] using hlarge
    have hprob := (hp.2 hlarge').le
    have hm := MeasureTheory.measureReal_mono (μ := μ)
      (Set.inter_subset_right :
        onlineActualT56JointEvent H K hH E fallback δ' 4 16 ∩
          onlineActualT56SimplifiedEvent H K hH E fallback δ' 4 16 ⊆
        onlineActualT56SimplifiedEvent H K hH E fallback δ' 4 16)
      (MeasureTheory.measure_ne_top μ _)
    have hsimple := hprob.trans hm
    simpa only [μ, planner, fallback, δ', onlineSourceOptimismDeltaPrime,
      onlineActualT56SimplifiedEvent, onlineW1SourceIota] using hsimple

theorem Thm5_2_corrected_holds : Thm5_2_corrected := by
  intro State Action _ _ H K hH hK E ρ δ hδ hδone
  refine ⟨4, 16, rfl, rfl, by norm_num, by norm_num, ?_⟩
  let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
  have hp := onlineUCBVI_actual_regret_high_probability H K hH hK E ρ fallback δ hδ hδone
  simpa [onlineUCBVIRegretRateEvent, onlineUCBVIRegretRate,
    onlineSourceOptimismDeltaPrime, onlineW1SourceIota, onlineActualEpisodeRegret,
    onlineCappedEpisodePolicyValue, fallback] using hp.le

theorem Lemma5_22_corrected_holds : Lemma5_22_corrected := by
  intro Ω _ μ _ X hX C hbound
  exact ⟨StatisticalRL.GeneralVariance.variance_square_le_four_of_abs_bound μ X hX C hbound,
    StatisticalRL.GeneralVariance.variance_centeredSquare_le_four_of_abs_bound μ X hX C hbound⟩


open StatisticalRL.OnlineRL.MVPProfile

theorem Lemma5_11_holds : Lemma5_11 := by
  intro State Action instState instStateNonempty instAction instActionNonempty
    K H hKpos hH hbudget
  have hsource := sourceMVPFinitePossibleProfiles_card_bound_all
    (K := K) (H := H) (Row := State × Action) hKpos hH
    (by
      simpa [Fintype.card_prod, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
        using hbudget)
  simpa [Fintype.card_prod, Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
    using hsource

theorem Lemma5_12_powerOfTwo_corrected_holds : Lemma5_12_powerOfTwo_corrected := by
  intro State Action _ _ _ _ H K hH hK row next
  let rowAt : ℕ → Fin H × (State × Action) :=
    fun n => (⟨n % H, Nat.mod_lt n hH⟩, row n)
  have hs : ∀ j, j < K * H → (rowAt j).1.val = j % H := by
    intro j hj
    rfl
  change (∑ k : Fin K, ∑ h : Fin H,
    (((max ((StatisticalRL.OnlineRL.onlineMVPCountTablesRun rowAt next (k.val * H)).stored
      (rowAt (k.val * H + h.val))) 1 : ℕ) : ℝ)⁻¹)) ≤ _
  rw [Finset.sum_comm]
  exact StatisticalRL.OnlineRL.onlineMVP_operationalHistory_sourceCountBudget H K hH hK rowAt next hs

end StatisticalRL.Statements
