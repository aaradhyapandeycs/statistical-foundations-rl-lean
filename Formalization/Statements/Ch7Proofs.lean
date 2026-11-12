import Formalization.Statements.Ch7
import Formalization.RobustRL.TVSourceMaximum
import Formalization.RobustRL.ChiSquaredSourceMaximum
import Formalization.Federated.LowerBound.UniversalConstant
import Formalization.RobustRL.LowerBounds.LowerBound73
import Formalization.RobustRL.LowerBounds.LowerBound75
import Formalization.RobustRL.LowerBounds.RandomizedLowerBound
import Formalization.MultiAgent.LowerBound.Main
import Formalization.Federated.Sync.Main
import Formalization.Federated.Sync.PerAgentSampleSize
import Formalization.RobustRL.DRVI.Thm74Main
import Formalization.RobustRL.DRVI.RobustQ
import Formalization.RLHF.VPO.Main
import Formalization.MultiAgent.ModelBased.Restricted
import Formalization.MultiAgent.Hedge.Main
import Formalization.RobustRL.DRVI.OraclePlannerMain
import Formalization.RobustRL.DRVI.OraclePlannerChiMain
import Formalization.RLHF.VPO.Reparameterization
import Formalization.TDInference.HalfSpace
import Formalization.TDInference.ClassicCLT
import Formalization.TDInference.Confidence.Intervals
import Formalization.TDInference.PluginCovariance.Basic
import Formalization.TDInference.PluginCovariance.Singular
import Formalization.TDInference.PluginCovariance.Consistency
import Formalization.TDInference.PluginCovariance.CorrectedConsistency
import Formalization.TDInference.PluginCovariance.PrintedLambdaRefutation
import Formalization.TDInference.PluginCovariance.Coverage
import Formalization.TDInference.PluginCovariance.IntervalRate
import Formalization.TDInference.PluginCovariance.EllipsoidRate
import Formalization.TDInference.PluginCovariance.RectangleRate
import Formalization.TDInference.Confidence.Regions
import Formalization.TDInference.Confidence.Calibration
import Formalization.TDInference.Confidence.ChiSquareQuantile
import Formalization.TDInference.PluginCovariance.Ellipsoid
import Formalization.RobustRL.DRVI.RobustBellmanDisplays
import Formalization.RLHF.VPO.Displays
import Formalization.MultiAgent.Equilibria
import Formalization.Probability.ConvexDistanceTV
import Formalization.TDInference.PluginCovariance.Rectangle
import Formalization.TDInference.ConvexSets.Sharp
import Formalization.TDInference.Confidence.RegionsSharp

open scoped BigOperators
namespace StatisticalRL.Statements.Ch7
universe u

theorem Lemma7_1_tv_holds : Lemma7_1_tv.{u} := by
  intro State instF instN p V σ hσ hV
  classical
  have hfeasible : StatisticalRL.RobustRL.tvFeasibleRow p σ =
      (fun q : StatisticalRL.FiniteDistribution State ↦
        (1 / 2 : ℝ) * ∑ s, |p.prob s - q.prob s| ≤ σ) := by
    funext q
    apply propext
    unfold StatisticalRL.RobustRL.tvFeasibleRow
    rw [StatisticalRL.RobustRL.eventTV_eq_finiteTotalVariation
      p.prob q.prob p.prob_nonneg q.prob_nonneg p.sum_prob q.sum_prob]
    rfl
  have hInf : StatisticalRL.RobustRL.tvPrimalInf p V σ =
      (⨅ q : {q : StatisticalRL.FiniteDistribution State //
        (1 / 2 : ℝ) * ∑ s, |p.prob s - q.prob s| ≤ σ},
        ∑ s, q.1.prob s * V s) := by
    unfold StatisticalRL.RobustRL.tvPrimalInf StatisticalRL.RobustRL.tvFeasibleRows
    rw [hfeasible]
    rfl
  obtain ⟨α, hα, heq, hmax⟩ :=
    StatisticalRL.RobustRL.TVProof.SourceMaximum.tvPrimalInf_eq_source_max p V σ hσ hV
  refine ⟨α, hα, ?_, ?_⟩
  · rw [← hInf]
    simpa [StatisticalRL.RobustRL.tvDualObjective,
      StatisticalRL.RobustRL.tvClipAbove, StatisticalRL.FiniteDistribution.expectation] using heq
  · intro β hβ
    simpa [StatisticalRL.RobustRL.tvDualObjective,
      StatisticalRL.RobustRL.tvClipAbove, StatisticalRL.FiniteDistribution.expectation] using hmax β hβ

private theorem valueMin_eq_global (State : Type*) [Fintype State] [Nonempty State]
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ) :
    StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.valueMin p V =
      Finset.univ.inf' Finset.univ_nonempty V := by
  classical
  apply le_antisymm
  · apply Finset.le_inf'
    intro s hs
    exact StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.valueMin_le p V s
  · unfold StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.valueMin
      StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.valueImage
    apply Finset.le_min'
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.inf'_le (s := Finset.univ) (f := V) hs

private theorem valueMax_eq_global (State : Type*) [Fintype State] [Nonempty State]
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ) :
    StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.valueMax p V =
      Finset.univ.sup' Finset.univ_nonempty V := by
  classical
  apply le_antisymm
  · have hmem : StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.valueMax p V ∈
        Finset.univ.image V := by
      unfold StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.valueMax
        StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.valueImage
      exact Finset.max'_mem _ _
    obtain ⟨s, hs, hvalue⟩ := Finset.mem_image.mp hmem
    calc
      StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.valueMax p V = V s := hvalue.symm
      _ ≤ Finset.univ.sup' Finset.univ_nonempty V := Finset.le_sup' (s := Finset.univ) (f := V) hs
  · apply Finset.sup'_le
    intro s hs
    exact StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.le_valueMax p V s

private theorem chiSquared_primal_set_eq
    {State : Type*} [Fintype State]
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ) (σ : ℝ) :
    {z : ℝ | ∃ q : StatisticalRL.FiniteDistribution State,
        (∀ s, p.prob s = 0 → q.prob s = 0) ∧
        (∑ s ∈ Finset.univ.filter (fun s ↦ 0 < p.prob s),
          (q.prob s - p.prob s) ^ 2 / p.prob s) ≤ σ ∧
        z = ∑ s, q.prob s * V s} =
      StatisticalRL.QLearning.qRobustExpectations p σ V := by
  classical
  ext z
  simp only [StatisticalRL.QLearning.qRobustExpectations, Set.mem_setOf_eq,
    StatisticalRL.QLearning.qChiBall]
  constructor
  · rintro ⟨q, hzero, hcost, hz⟩
    refine ⟨q, ⟨hzero, ?_⟩, ?_⟩
    · simpa [StatisticalRL.QLearning.qChiSquared] using hcost
    · simpa [StatisticalRL.FiniteDistribution.expectation] using hz
  · rintro ⟨q, ⟨hzero, hcost⟩, hz⟩
    refine ⟨q, hzero, ?_, ?_⟩
    · simpa [StatisticalRL.QLearning.qChiSquared] using hcost
    · simpa [StatisticalRL.FiniteDistribution.expectation] using hz

/-- The two source bullets of Lemma 7.1 consume the already proved TV and χ²
maximum theorems. No optimization argument is reproved here. -/
theorem Lemma7_1_holds : Lemma7_1 := by
  intro State instF instN p V σ hσ hV
  classical
  have htv := Lemma7_1_tv_holds State p V σ hσ hV
  refine ⟨htv, ?_⟩
  · obtain ⟨q, α, hq, hα, hpay, hinf, hmax⟩ :=
      StatisticalRL.RobustRL.ChiSquaredSourceMaximum.chiSquared_source_maximum p V σ hσ hV
    have hprimal := chiSquared_primal_set_eq p V σ
    have hmin := valueMin_eq_global State p V
    have hmaxval := valueMax_eq_global State p V
    have hαglobal : α ∈ Set.Icc
        (Finset.univ.inf' Finset.univ_nonempty V)
        (Finset.univ.sup' Finset.univ_nonempty V) := by
      simpa [hmin, hmaxval] using hα
    have heq : (sInf {z : ℝ | ∃ q : StatisticalRL.FiniteDistribution State,
        (∀ s, p.prob s = 0 → q.prob s = 0) ∧
        (∑ s ∈ Finset.univ.filter (fun s ↦ 0 < p.prob s),
          (q.prob s - p.prob s) ^ 2 / p.prob s) ≤ σ ∧
        z = ∑ s, q.prob s * V s}) =
        (∑ s, p.prob s * min (V s) α) - Real.sqrt (σ *
          ((∑ s, p.prob s * (min (V s) α) ^ 2) -
            (∑ s, p.prob s * min (V s) α) ^ 2)) := by
      calc
        _ = sInf (StatisticalRL.QLearning.qRobustExpectations p σ V) := by
          rw [hprimal]
        _ = StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.dualObjective p V σ α := hinf
        _ = _ := by
          simp [StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.dualObjective,
            StatisticalRL.FiniteDistribution.variance,
            StatisticalRL.FiniteDistribution.expectation]
    refine ⟨α, hαglobal, heq, ?_⟩
    intro β hβ
    have hβ' : β ∈ Set.Icc
        (StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.valueMin p V)
        (StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.valueMax p V) := by
      simpa [hmin, hmaxval] using hβ
    have hmax' := hmax β hβ'
    simpa [StatisticalRL.RobustRL.ChiSquaredPrimalDualWeakBridge.dualObjective,
      StatisticalRL.FiniteDistribution.variance,
      StatisticalRL.FiniteDistribution.expectation] using hmax'


/-- `Thm7_10_restricted` from `lowerBound_of_fewRounds_onRange` with `c₀ = 1`,
`C_γ = lbConst 1 γ`. -/
theorem Thm7_10_restricted_holds : Thm7_10_restricted := by
  refine ⟨1, one_pos, StatisticalRL.Ch7Rest.FedGeneric.lbConst 1, fun γ hγ hγ1 ↦
    ⟨StatisticalRL.Ch7Rest.FedGeneric.lbConst_pos 1 γ (by linarith) hγ1, ?_⟩⟩
  intro State Action _ _ hS hA T B 𝒞 η hT _ hB _ hT𝒞 hη hround
  obtain ⟨M, hM, hK⟩ := StatisticalRL.Ch7Rest.FedGeneric.lowerBound_of_fewRounds_onRange 1 γ
    (by linarith) hγ1 State Action (by omega) (by omega) T B 𝒞 η hT hB hT𝒞
    (StatisticalRL.Ch7Rest.FedGeneric.printedRates_mem_Icc γ hγ1 T η hη) hround
  exact ⟨M, hM, fun K hK2 ↦ hK K (by omega)⟩

/-- `Thm7_3_corrected` from `StatisticalRL.RobustRL.Ch7.LowerBound73.thm7_3_corrected`. -/
theorem Thm7_3_corrected_holds : Thm7_3_corrected :=
  StatisticalRL.RobustRL.Ch7.LowerBound73.thm7_3_corrected

/-- `Thm7_3_corrected_knownReward` from
`StatisticalRL.RobustRL.Ch7.LowerBound73.thm7_3_corrected_knownReward`. -/
theorem Thm7_3_corrected_knownReward_holds : Thm7_3_corrected_knownReward :=
  StatisticalRL.RobustRL.Ch7.LowerBound73.thm7_3_corrected_knownReward

/-- `Thm7_5_corrected` from `StatisticalRL.RobustRL.Ch7.LowerBound75.thm7_5_corrected`. -/
theorem Thm7_5_corrected_holds : Thm7_5_corrected :=
  StatisticalRL.RobustRL.Ch7.LowerBound75.thm7_5_corrected

/-- `Thm7_5_corrected_knownReward` from
`StatisticalRL.RobustRL.Ch7.LowerBound75.thm7_5_corrected_knownReward`. -/
theorem Thm7_5_corrected_knownReward_holds : Thm7_5_corrected_knownReward :=
  StatisticalRL.RobustRL.Ch7.LowerBound75.thm7_5_corrected_knownReward

/-- `Thm7_3_corrected_randomized` from `StatisticalRL.RobustRL.Ch7.RandomizedLowerBound.thm7_3_corrected_randomized`. -/
theorem Thm7_3_corrected_randomized_holds : Thm7_3_corrected_randomized.{u} :=
  StatisticalRL.RobustRL.Ch7.RandomizedLowerBound.thm7_3_corrected_randomized.{u}

/-- `Thm7_3_corrected_knownReward_randomized` from `StatisticalRL.RobustRL.Ch7.RandomizedLowerBound.thm7_3_corrected_knownReward_randomized`. -/
theorem Thm7_3_corrected_knownReward_randomized_holds : Thm7_3_corrected_knownReward_randomized.{u} :=
  StatisticalRL.RobustRL.Ch7.RandomizedLowerBound.thm7_3_corrected_knownReward_randomized.{u}

/-- `Thm7_5_corrected_randomized` from `StatisticalRL.RobustRL.Ch7.RandomizedLowerBound.thm7_5_corrected_randomized`. -/
theorem Thm7_5_corrected_randomized_holds : Thm7_5_corrected_randomized.{u} :=
  StatisticalRL.RobustRL.Ch7.RandomizedLowerBound.thm7_5_corrected_randomized.{u}

/-- `Thm7_5_corrected_knownReward_randomized` from `StatisticalRL.RobustRL.Ch7.RandomizedLowerBound.thm7_5_corrected_knownReward_randomized`. -/
theorem Thm7_5_corrected_knownReward_randomized_holds : Thm7_5_corrected_knownReward_randomized.{u} :=
  StatisticalRL.RobustRL.Ch7.RandomizedLowerBound.thm7_5_corrected_knownReward_randomized.{u}

/-- `Thm7_8_corrected` from `StatisticalRL.Ch7Rest.Marl.thm7_8_corrected`. -/
theorem Thm7_8_corrected_holds : Thm7_8_corrected :=
  StatisticalRL.Ch7Rest.Marl.thm7_8_corrected

/-- `Thm7_8_corrected_constSum` from `StatisticalRL.Ch7Rest.Marl.thm7_8_corrected_constSum`. -/
theorem Thm7_8_corrected_constSum_holds : Thm7_8_corrected_constSum :=
  StatisticalRL.Ch7Rest.Marl.thm7_8_corrected_constSum

/-- `Thm7_9_corrected` from `StatisticalRL.Ch7Rest.FedSync.fedSynQ_error_le_of_eta_le_one`
(constants `c_T = 10⁴`, `c_η = 1/216`; `η < 1` gives the export's `η ≤ 1`). -/
theorem Thm7_9_corrected_holds : Thm7_9_corrected :=
  ⟨10000, 1 / 216, by norm_num, by norm_num,
    fun _State _Action _ _ M K τ T δ ε Q₀ hK hτ hT _hτT _hγ hδ hδ1 hε hεH hQ₀ η hη hη1 hτc hTc =>
      StatisticalRL.Ch7Rest.FedSync.fedSynQ_error_le_of_eta_le_one M K τ T δ ε Q₀ hK hτ hT hδ
        hδ1 hε hεH hQ₀ η hη hη1.le hτc hTc⟩

/-- `Eq_sample_size_per_agent_fedQ_restricted` from
`StatisticalRL.Ch7Rest.FedSync.fedSynQ_readOff_restricted` (`C = 270000216`, `c_η = 1/216`). -/
theorem Eq_sample_size_per_agent_fedQ_restricted_holds :
    Eq_sample_size_per_agent_fedQ_restricted :=
  ⟨270000216, 1 / 216, by norm_num, by norm_num,
    fun _State _Action _ _ M K δ ε Q₀ hK hδ hδ1 hε hεH hQ₀ hKr =>
      StatisticalRL.Ch7Rest.FedSync.fedSynQ_readOff_restricted M K δ ε Q₀ hK hδ hδ1 hε hεH hQ₀
        hKr⟩

/-- `Thm7_2_corrected` from `StatisticalRL.RobustRL.DRVI.thm7_2_corrected_holds`
(`C₁ = 2`, `C₂ = 10⁶`). -/
theorem Thm7_2_corrected_holds : Thm7_2_corrected :=
  StatisticalRL.RobustRL.DRVI.thm7_2_corrected_holds

/-- `Remark7_1_restricted` from `StatisticalRL.RobustRL.DRVI.tv_oracle_planner_guarantee`
(`C₂ = max(10⁶, 2 c_opt)`). -/
theorem Remark7_1_restricted_holds : Remark7_1_restricted :=
  StatisticalRL.RobustRL.DRVI.tv_oracle_planner_guarantee

/-- Drift guard: the library copy `StatisticalRL.RobustRL.Ch7.Thm7_2_corrected` of `Thm7_2_corrected` is definitionally the statement-index
entry, so any divergence breaks the build. -/
theorem Thm7_2_corrected_iff_library :
    Thm7_2_corrected ↔ StatisticalRL.RobustRL.Ch7.Thm7_2_corrected :=
  Iff.rfl

/-- `Remark7_2_restricted` from `StatisticalRL.RobustRL.DRVI.chi_oracle_planner_guarantee`
(`c₂ = 10⁶ + 8 c_opt`). -/
theorem Remark7_2_restricted_holds : Remark7_2_restricted :=
  StatisticalRL.RobustRL.DRVI.chi_oracle_planner_guarantee

/-- `Thm7_4_corrected` from `StatisticalRL.RobustRL.DRVI.thm7_4_corrected_holds`
(`c₁ = 2`, `c₂ = 10⁶`). -/
theorem Thm7_4_corrected_holds : Thm7_4_corrected :=
  StatisticalRL.RobustRL.DRVI.thm7_4_corrected_holds

section Thm7_12

/-- Drift guard: the library copy `StatisticalRL.RobustRL.Ch7.Thm7_4_corrected` of `Thm7_4_corrected` is definitionally the statement-index
entry, so any divergence breaks the build. -/
theorem Thm7_4_corrected_iff_library :
    Thm7_4_corrected ↔ StatisticalRL.RobustRL.Ch7.Thm7_4_corrected :=
  Iff.rfl

open StatisticalRL.Ch7Rest.Rlhf in
theorem Thm7_12_corrected_holds : Thm7_12_corrected := by
  intro X Y _ _ d T ρ π_ref π_cal φ θstar β r_max α δ hd hT hρ hρ1 href hcal hφ hβ hR hθs hα hδ
  refine ⟨exists_ballSelection ρ href π_cal hcal.2 φ α hβ hR.le, fun sel hsel ↦ ?_⟩
  refine le_trans (vpo_regret_both ρ π_ref π_cal φ θstar hd hT hρ hρ1 href hcal hφ hβ hR hθs hα
    hδ sel hsel) (Finset.sum_le_sum fun h _ ↦ mul_le_mul_of_nonneg_left ?_
      (vpoTrajWeight_nonneg ρ π_ref φ θstar β sel hρ href h))
  split_ifs with h1 h2 <;> first | exact absurd h1.1 h2 | norm_num

open StatisticalRL.Ch7Rest.Rlhf in
theorem Thm7_12_corrected_local_holds : Thm7_12_corrected_local := by
  intro X Y _ _ d T ρ π_ref π_cal φ θstar β r_max α δ hd hT hρ hρ1 href hcal hφ hβ hR hθs hα hδ
  refine ⟨exists_ballSelection ρ href π_cal hcal.2 φ α hβ hR.le, fun sel hsel ↦ ?_⟩
  refine le_trans (vpo_regret_both ρ π_ref π_cal φ θstar hd hT hρ hρ1 href hcal hφ hβ hR hθs hα
    hδ sel hsel) (Finset.sum_le_sum fun h _ ↦ mul_le_mul_of_nonneg_left ?_
      (vpoTrajWeight_nonneg ρ π_ref φ θstar β sel hρ href h))
  split_ifs with h1 h2 <;> first | exact absurd h1.2 h2 | norm_num

end Thm7_12

section Eq_DPO_VPO

open StatisticalRL.Ch7Rest.Rlhf in
theorem Eq_DPO_restricted_holds : Eq_DPO_restricted := by
  intro X Y _ _ π_ref β D href hβ
  exact ⟨fun r ↦ dpoLoss_gibbs href hβ.ne' r D,
    fun _ hπ ↦ exists_gibbsPolicy_eq href hβ.ne' hπ,
    gibbsPolicy_eq_iff href hβ.ne',
    fun _ hπ ↦ dpo_argmin_iff href hβ.ne' D hπ⟩

open StatisticalRL.Ch7Rest.Rlhf in
theorem Eq_policy_RBMLE_restricted_holds : Eq_policy_RBMLE_restricted := by
  intro X Y _ _ ρ π_ref π_cal sign α β D href hρ hcal hβ _ _
  refine ⟨fun r ↦ (vpoObjective_gibbs_optCal ρ hρ href π_cal hcal (sign * α) hβ r D).symm,
    fun _ hπ ↦ vpo_argmin_iff ρ hρ href π_cal hcal (sign * α) hβ D hπ,
    fun _ hπ ↦ calShift_eq_neg_kl ρ hcal.1 hπ.1,
    ⟨sign * α * β * ∑ x, ρ x * ∑ y, π_cal x y * (Real.log (π_cal x y) - Real.log (π_ref x y)),
      fun π _ ↦ vpoObjective_calSwap ρ π_cal (sign * α) β D π⟩⟩

open StatisticalRL.Ch7Rest.Rlhf in
theorem Eq_online_RBMLE_restricted_holds : Eq_online_RBMLE_restricted := by
  intro X Y _ _ ρ π_ref π_cal α β D href hρ hcal hβ _ _ r hr
  exact online_vpo_step ρ hρ href π_cal hcal α hβ D r hr

end Eq_DPO_VPO

section RLHFDisplaysProofs

open StatisticalRL.Ch7Rest.Rlhf in
/-- `Eq_reward_policy_eq_restricted` from `reward_eq_log_gibbs` (`RLHF/VPO/Displays.lean`). -/
theorem Eq_reward_policy_eq_restricted_holds : Eq_reward_policy_eq_restricted := by
  intro X Y _ _ π_ref β href hβ r x y
  exact reward_eq_log_gibbs href hβ r x y

open StatisticalRL.Ch7Rest.Rlhf in
/-- `Eq_Jstar_restricted` from `optCalValue_printed_lines` (`RLHF/VPO/Displays.lean`). -/
theorem Eq_Jstar_restricted_holds : Eq_Jstar_restricted := by
  intro X Y _ _ ρ π_ref π_cal β href hρ hcal hβ r
  exact optCalValue_printed_lines ρ hρ href π_cal hcal hβ r

open StatisticalRL.Ch7Rest.Rlhf in
/-- `Eq_RLHF_policy_closed_form_restricted` from `gibbsPolicy_isCondPolicy` (`RLHF/VPO/Gibbs.lean`),
`klValue_le_gibbs` and `isMaximizer_klValue_iff` (`RLHF/VPO/Displays.lean`). -/
theorem Eq_RLHF_policy_closed_form_restricted_holds : Eq_RLHF_policy_closed_form_restricted := by
  intro X Y _ _ ρ π_ref β href hρ hβ r J πr
  exact ⟨gibbsPolicy_isCondPolicy href r β, fun π hπ ↦ klValue_le_gibbs ρ hρ href hβ r π hπ,
    fun π hπ ↦ isMaximizer_klValue_iff ρ hρ href hβ r π hπ⟩

open StatisticalRL.Ch7Rest.Rlhf in
/-- `Eq_calibrated_value_shiftInvariant_restricted` from `prompt_shift_invariance`
(`RLHF/VPO/Displays.lean`). -/
theorem Eq_calibrated_value_shiftInvariant_restricted_holds :
    Eq_calibrated_value_shiftInvariant_restricted := by
  intro X Y _ _ ρ π_ref π_cal β href hρ hcal hβ r₂ c r₁ nll J Jcal
  obtain ⟨h0, h1, h2, h3, h4⟩ := prompt_shift_invariance ρ hρ href π_cal hcal hβ r₂ c
  exact ⟨h0, h1, h4, h2, h3⟩

end RLHFDisplaysProofs

section Thm7_6

/-- `Thm7_6_restricted` from `StatisticalRL.Ch7Rest.Marl76.thm7_6_restricted` (`C₁ = 400`). -/
theorem Thm7_6_restricted_holds : Thm7_6_restricted :=
  StatisticalRL.Ch7Rest.Marl76.thm7_6_restricted

end Thm7_6

/-- Drift guard: the library copy `StatisticalRL.Ch7Rest.Marl76.Thm7_6_restricted` of `Thm7_6_restricted` is definitionally the statement-index
entry, so any divergence breaks the build. -/
theorem Thm7_6_restricted_iff_library :
    Thm7_6_restricted ↔ StatisticalRL.Ch7Rest.Marl76.Thm7_6_restricted :=
  Iff.rfl

section Thm7_7

/-- `Thm7_7_restricted` from `StatisticalRL.Ch7Rest.Marl77.thm7_7_restricted` (`C = 20000`). -/
theorem Thm7_7_restricted_holds : Thm7_7_restricted :=
  StatisticalRL.Ch7Rest.Marl77.thm7_7_restricted

end Thm7_7

/-- Drift guard: the library copy `StatisticalRL.Ch7Rest.Marl77.Thm7_7_restricted` of `Thm7_7_restricted` is definitionally the statement-index
entry, so any divergence breaks the build. -/
theorem Thm7_7_restricted_iff_library :
    Thm7_7_restricted ↔ StatisticalRL.Ch7Rest.Marl77.Thm7_7_restricted :=
  Iff.rfl

section Eq_mdp_value_Q_restricted

open StatisticalRL StatisticalRL.RobustRL.Ch7 StatisticalRL.RobustRL.DRVI in
/-- `Eq_mdp_value_Q_restricted` from `StatisticalRL.RobustRL.DRVI.exists_det_robust_value_Q_optimal`
(`f = optPolicy`, greedy for the robust optimality fixed point), with `RowAttains` from
`tvBall_family_rowAttains` / `chiBall_family_rowAttains` or from the attainment hypothesis. -/
theorem Eq_mdp_value_Q_restricted_holds : Eq_mdp_value_Q_restricted := by
  intro State Action _ _ M σ hσ ball hball
  have hU : ∀ s a, RowAttains (ball (M.transition s a) σ) := by
    rcases hball with rfl | rfl | hatt
    · exact tvBall_family_rowAttains M hσ.le
    · exact chiBall_family_rowAttains M hσ.le
    · exact fun s a V ↦ hatt s a V
  exact exists_det_robust_value_Q_optimal ball M σ hU

end Eq_mdp_value_Q_restricted

section RobustBellmanProofs
universe v

open StatisticalRL StatisticalRL.RobustRL.Ch7 StatisticalRL.RobustRL.DRVI in
/-- `Eq_bellman_equ_infinite_all_restricted` from `robustPolicyQ_eq_reward_add_iInf`,
`sSup_robustPolicyQ_eq_reward_add_iInf`, `robustPolicyValue_eq_optFix_of_dominates`,
`robustPolicyQ_eq_optQ_of_dominates` (`RobustBellmanDisplays.lean`), with `RowAttains` from
`tvBall_family_rowAttains` / `chiBall_family_rowAttains` or from the attainment hypothesis. -/
theorem Eq_bellman_equ_infinite_all_restricted_holds :
    Eq_bellman_equ_infinite_all_restricted.{u, v} := by
  intro State Action _ _ M σ hσ ball hball
  have hU : ∀ s a, RowAttains (ball (M.transition s a) σ) := by
    rcases hball with rfl | rfl | hatt
    · exact tvBall_family_rowAttains M hσ.le
    · exact chiBall_family_rowAttains M hσ.le
    · exact fun s a V ↦ hatt s a V
  refine ⟨robustPolicyQ_eq_reward_add_iInf ball M σ hU,
    sSup_robustPolicyQ_eq_reward_add_iInf ball M σ hU, fun πs h ↦ ⟨fun s ↦ ?_, fun s a ↦ ?_⟩⟩
  · rw [robustPolicyValue_eq_optFix_of_dominates ball M σ hU πs h,
      robustOptimalValue_eq_optFix ball M σ hU]
  · rw [robustPolicyQ_eq_optQ_of_dominates ball M σ hU πs h, sSup_robustPolicyQ_eq_optQ ball M σ hU]

open StatisticalRL StatisticalRL.RobustRL.Ch7 StatisticalRL.RobustRL.DRVI in
/-- `Eq_robust_bellman_fixedPoint_restricted` from `robustPolicyQ_eq_optQ_of_dominates`,
`robustBellman_optQ`, `eq_optQ_of_robustBellman`, `norm_robustBellman_sub_le`,
`norm_robustBellman_iterate_sub_le`, `drviIterate_eq_iterate` (`RobustBellmanDisplays.lean`) and
`drviIterate_error` (`Planning.lean`). -/
theorem Eq_robust_bellman_fixedPoint_restricted_holds :
    Eq_robust_bellman_fixedPoint_restricted.{u, v} := by
  intro State Action _ _ M σ hσ ball hball πs h T Qs
  have hU : ∀ s a, RowAttains (ball (M.transition s a) σ) := by
    rcases hball with rfl | rfl | hatt
    · exact tvBall_family_rowAttains M hσ.le
    · exact chiBall_family_rowAttains M hσ.le
    · exact fun s a V ↦ hatt s a V
  have hT : T = robustBellman ball M σ :=
    funext fun Q ↦ (robustBellman_eq_inline ball M σ Q).symm
  have hQs : Qs = optQ (ballFamily ball M σ) M :=
    robustPolicyQ_eq_optQ_of_dominates ball M σ hU πs h
  clear_value T Qs
  subst hT hQs
  refine ⟨robustBellman_optQ ball M σ, fun Q hQ ↦ eq_optQ_of_robustBellman ball M σ hQ,
    norm_robustBellman_sub_le ball M σ,
    fun Q₀ t ↦ norm_robustBellman_iterate_sub_le ball M σ (robustBellman_optQ ball M σ) Q₀ t,
    fun t s a ↦ ?_⟩
  rw [← drviIterate_eq_iterate]
  exact drviIterate_error ball M σ (fun s a ↦ (hU s a).nonempty) t s a

end RobustBellmanProofs

section Thm7_11

/-- `Thm7_11_corrected` from
`StatisticalRL.Ch7Rest.TDInference.abs_lawProb_convex_sub_gaussCov_le_third_sharp`
(the export needs only `η₀ ≤ 1`). -/
theorem Thm7_11_corrected_holds : Thm7_11_corrected := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  exact StatisticalRL.Ch7Rest.TDInference.abs_lawProb_convex_sub_gaussCov_le_third_sharp M π μ h0
    (by linarith) V₀ hμ hΓ

/-- `Thm7_11_corrected_halfspace` from
`StatisticalRL.Ch7Rest.TDInference.abs_lawProb_halfSpace_sub_gaussCov_le`
(the export needs only `η₀ ≤ 1`). -/
theorem Thm7_11_corrected_halfspace_holds : Thm7_11_corrected_halfspace := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  exact StatisticalRL.Ch7Rest.TDInference.abs_lawProb_halfSpace_sub_gaussCov_le M π μ h0
    (by linarith) V₀ hμ hΓ

end Thm7_11

section EqClassicCltProofs

/-- `Eq_classic_clt_corrected` from
`StatisticalRL.Ch7Rest.TDInference.tendsto_sum_pathWeight_bcf_gaussCov` (the export needs only
`η₀ ≤ 1`). -/
theorem Eq_classic_clt_corrected_holds : Eq_classic_clt_corrected := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 g
  exact StatisticalRL.Ch7Rest.TDInference.tendsto_sum_pathWeight_bcf_gaussCov M π μ hμ h0
    (by linarith) V₀ g

/-- `Eq_classic_clt_restricted` from
`StatisticalRL.Ch7Rest.TDInference.tendsto_sum_pathWeight_bcf_gaussCov_printed_of_reward_const`. -/
theorem Eq_classic_clt_restricted_holds : Eq_classic_clt_restricted := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hr hμ h0 h1 g
  exact StatisticalRL.Ch7Rest.TDInference.tendsto_sum_pathWeight_bcf_gaussCov_printed_of_reward_const
    M π μ hr hμ h0 (by linarith) V₀ g

end EqClassicCltProofs

section EqConvexCdeltaProofs

/-- `Eq_convex_Cdelta_corrected_oracle` from
`StatisticalRL.Ch7Rest.TDInference.exists_coverage_oracle_bounds` (the export needs only `η₀ ≤ 1`). -/
theorem Eq_convex_Cdelta_corrected_oracle_holds : Eq_convex_Cdelta_corrected_oracle := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  exact StatisticalRL.Ch7Rest.TDInference.exists_coverage_oracle_bounds M π μ h0 (by linarith) V₀
    hμ hΓ

/-- `Eq_convex_Cdelta_corrected_plugin` from
`StatisticalRL.Ch7Rest.TDInference.plugin_coverage_rate` (the export needs only `η₀ ≤ 1`). -/
theorem Eq_convex_Cdelta_corrected_plugin_holds : Eq_convex_Cdelta_corrected_plugin := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  exact StatisticalRL.Ch7Rest.TDInference.plugin_coverage_rate M π μ h0 (by linarith) V₀ hμ hΓ

/-- `Eq_convex_Cdelta_fixedShape_corrected_oracle` from
`StatisticalRL.Ch7Rest.TDInference.exists_confRegion_oracle_bounds_sharp` (the export needs only `η₀ ≤ 1`). -/
theorem Eq_convex_Cdelta_fixedShape_corrected_oracle_holds :
    Eq_convex_Cdelta_fixedShape_corrected_oracle := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  obtain ⟨K₀, hK₀, hb⟩ := StatisticalRL.Ch7Rest.TDInference.exists_confRegion_oracle_bounds_sharp
    M π μ h0 (by linarith) V₀ hμ hΓ
  exact ⟨K₀, hK₀, fun T hT ↦ (hb T hT).1⟩

/-- `Eq_convex_Cdelta_ellipsoid_corrected_oracle` from
`StatisticalRL.Ch7Rest.TDInference.exists_confRegion_oracle_bounds_sharp` (the export needs only `η₀ ≤ 1`
and holds for every `q`). -/
theorem Eq_convex_Cdelta_ellipsoid_corrected_oracle_holds :
    Eq_convex_Cdelta_ellipsoid_corrected_oracle := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  obtain ⟨K₀, hK₀, hb⟩ := StatisticalRL.Ch7Rest.TDInference.exists_confRegion_oracle_bounds_sharp
    M π μ h0 (by linarith) V₀ hμ hΓ
  exact ⟨K₀, hK₀, fun T hT q _ ↦ (hb T hT).2.1 q⟩

/-- `Eq_convex_Cdelta_rectangle_corrected_oracle` from
`StatisticalRL.Ch7Rest.TDInference.exists_confRegion_oracle_bounds_sharp` (the export needs only `η₀ ≤ 1`
and holds for every `r`). -/
theorem Eq_convex_Cdelta_rectangle_corrected_oracle_holds :
    Eq_convex_Cdelta_rectangle_corrected_oracle := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  obtain ⟨K₀, hK₀, hb⟩ := StatisticalRL.Ch7Rest.TDInference.exists_confRegion_oracle_bounds_sharp
    M π μ h0 (by linarith) V₀ hμ hΓ
  exact ⟨K₀, hK₀, fun T hT r _ ↦ (hb T hT).2.2 r⟩

/-- `Eq_convex_Cdelta_ellipsoid_corrected_oracle_calibrated` from
`StatisticalRL.Ch7Rest.TDInference.exists_confRegion_oracle_calibrated_sharp` (the export needs only
`η₀ ≤ 1`; the ellipsoid component is taken). -/
theorem Eq_convex_Cdelta_ellipsoid_corrected_oracle_calibrated_holds :
    Eq_convex_Cdelta_ellipsoid_corrected_oracle_calibrated := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  obtain ⟨K₀, hK₀, hb⟩ := StatisticalRL.Ch7Rest.TDInference.exists_confRegion_oracle_calibrated_sharp
    M π μ hμ h0 (by linarith) V₀ hΓ
  refine ⟨K₀, hK₀, fun α hα0 hα1 ↦ ?_⟩
  obtain ⟨q, hq0, _, _, hq, _, hT⟩ := hb α hα0 hα1
  exact ⟨q, hq0, hq, fun T hT1 ↦ (hT T hT1).1⟩

/-- `Eq_convex_Cdelta_rectangle_corrected_oracle_calibrated` from
`StatisticalRL.Ch7Rest.TDInference.exists_confRegion_oracle_calibrated_sharp` (the export needs only
`η₀ ≤ 1`; the rectangle component is taken). -/
theorem Eq_convex_Cdelta_rectangle_corrected_oracle_calibrated_holds :
    Eq_convex_Cdelta_rectangle_corrected_oracle_calibrated := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  obtain ⟨K₀, hK₀, hb⟩ := StatisticalRL.Ch7Rest.TDInference.exists_confRegion_oracle_calibrated_sharp
    M π μ hμ h0 (by linarith) V₀ hΓ
  refine ⟨K₀, hK₀, fun α hα0 hα1 ↦ ?_⟩
  obtain ⟨_, _, r, hr0, _, hr, hT⟩ := hb α hα0 hα1
  exact ⟨r, hr0, hr, fun T hT1 ↦ (hT T hT1).2⟩

/-- `Eq_convex_Cdelta_ellipsoid_corrected_oracle_chiSquared` from
`StatisticalRL.Ch7Rest.TDInference.exists_confRegion_oracle_chiSquared_sharp` (the export needs only `η₀ ≤ 1`)
and `StatisticalRL.Ch7Rest.TDInference.exists_chiSquared_quantile`. -/
theorem Eq_convex_Cdelta_ellipsoid_corrected_oracle_chiSquared_holds :
    Eq_convex_Cdelta_ellipsoid_corrected_oracle_chiSquared := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  obtain ⟨K₀, hK₀, hb⟩ := StatisticalRL.Ch7Rest.TDInference.exists_confRegion_oracle_chiSquared_sharp
    M π μ hμ h0 (by linarith) V₀ hΓ
  refine ⟨K₀, hK₀, fun α hα0 hα1 ↦ ⟨?_, fun R hR ↦ hb α hα0 hα1 R hR⟩⟩
  exact StatisticalRL.Ch7Rest.TDInference.exists_chiSquared_quantile Fintype.card_pos hα0 hα1

/-- `Eq_convex_Cdelta_ellipsoid_corrected_plugin` from
`StatisticalRL.Ch7Rest.TDInference.exists_coverage_ellipsoid_plugin_rate` (the export needs only `η₀ ≤ 1`); the
`χ²(S)` form is the same bound at `q = R`. -/
theorem Eq_convex_Cdelta_ellipsoid_corrected_plugin_holds :
    Eq_convex_Cdelta_ellipsoid_corrected_plugin := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  obtain ⟨K, hK, hb⟩ := StatisticalRL.Ch7Rest.TDInference.exists_coverage_ellipsoid_plugin_rate
    M π μ h0 (by linarith) V₀ hμ hΓ
  refine ⟨K, hK, fun T hT q ↦ hb T hT q, fun α _ _ R hR T hT ↦ ?_⟩
  rw [← hR]
  exact hb T hT R

open StatisticalRL.Ch7Rest.TDInference in
/-- `Eq_convex_Cdelta_rectangle_corrected_plugin` from
`StatisticalRL.Ch7Rest.TDInference.exists_coverage_rect_plugin_rate`, with `posSemidef_lambdaHat`,
`isSupBoxQuantile_supBoxQuantile` and `gaussOfCov_eq_map` for the existence conjunct and the law of `Q Z`. -/
theorem Eq_convex_Cdelta_rectangle_corrected_plugin_holds :
    Eq_convex_Cdelta_rectangle_corrected_plugin := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ α hα0 hα1
  have h1' : η₀ ≤ 1 := by linarith
  refine ⟨⟨fun _ ω ↦ supBoxQuantile (lambdaHat M η₀ V₀ ω) α, fun T ω ↦ ?_⟩, ?_⟩
  · have hS := posSemidef_lambdaHat M η₀ V₀ ω
    obtain ⟨Q, hQ⟩ := StatisticalRL.Probability.exists_mul_transpose_eq_of_posSemidef hS
    have hG := gaussOfCov_eq_map hS Q hQ
    obtain ⟨q1, q2⟩ := isSupBoxQuantile_supBoxQuantile (lambdaHat M η₀ V₀ ω) hα0 hα1
    refine ⟨Q, hQ, fun r hr ↦ q1 r ?_, fun r hr ↦ q2 r ?_⟩
    · rw [supBoxProb, hG]; exact hr
    · rw [supBoxProb, hG]; exact hr
  · obtain ⟨K, hK, hb⟩ := exists_coverage_rect_plugin_rate M π μ h0 h1' V₀ hμ hΓ hα0 hα1
    refine ⟨K, hK, fun rhat hrhat ↦ hb rhat fun T ω ↦ ?_⟩
    obtain ⟨Q, hQ, q1, q2⟩ := hrhat T ω
    have hG := gaussOfCov_eq_map (posSemidef_lambdaHat M η₀ V₀ ω) Q hQ
    refine ⟨fun r hr ↦ q1 r ?_, fun r hr ↦ q2 r ?_⟩
    · rw [supBoxProb, hG] at hr; exact hr
    · rw [supBoxProb, hG] at hr; exact hr

end EqConvexCdeltaProofs

section EqDefnHatLambdaProofs

/-- `Eq_defn_hat_Lambda_corrected` from
`StatisticalRL.Ch7Rest.TDInference.eq_defn_hat_Lambda_corrected` (the export needs only `η₀ ≤ 1`). -/
theorem Eq_defn_hat_Lambda_corrected_holds : Eq_defn_hat_Lambda_corrected := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 ε hε
  exact StatisticalRL.Ch7Rest.TDInference.eq_defn_hat_Lambda_corrected State Action M π μ η₀ V₀ hμ
    h0 (by linarith) ε hε

/-- `Eq_defn_hat_Lambda_restricted` from
`StatisticalRL.Ch7Rest.TDInference.eq_defn_hat_Lambda_restricted` (the export needs only
`η₀ ≤ 1`). -/
theorem Eq_defn_hat_Lambda_restricted_holds : Eq_defn_hat_Lambda_restricted := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hr hμ h0 h1 ε hε
  exact StatisticalRL.Ch7Rest.TDInference.eq_defn_hat_Lambda_restricted M π μ η₀ V₀ hr hμ h0
    (by linarith) hε

end EqDefnHatLambdaProofs

section MarlEquilibriaProofs

/-- `Marl_bestResponse_exists` from the library exports `valueJ_deviate_le_starValue`,
`valueJ_brPolicy_eq_starValue` (witness `brPolicy`), `starValue_terminal` and
`starValue_bellman` (namespace `Marl76`). -/
theorem Marl_bestResponse_exists_holds : Marl_bestResponse_exists := by
  intro m S H A G π i hAi
  exact ⟨fun π' h _ _ s => StatisticalRL.Ch7Rest.Marl76.valueJ_deviate_le_starValue G π i π' h s,
    ⟨StatisticalRL.Ch7Rest.Marl76.brPolicy G π i hAi, fun h _ hh s =>
      StatisticalRL.Ch7Rest.Marl76.valueJ_brPolicy_eq_starValue G π i hAi h (by omega) s⟩,
    fun s => StatisticalRL.Ch7Rest.Marl76.starValue_terminal G π i hAi s,
    fun h _ hh s => StatisticalRL.Ch7Rest.Marl76.starValue_bellman G π i hAi h hh s⟩

/-- `Marl_NE_isCCE_not_converse` from the library exports `isCCE_of_isNE_of_prob_eq`,
`coordGame_reward_mem`, `coordPolicy_isCCE` and `coordPolicy_not_product` (namespace `Marl76`). -/
theorem Marl_NE_isCCE_not_converse_holds : Marl_NE_isCCE_not_converse :=
  ⟨fun _ _ _ _ G σ π hπ hNE => StatisticalRL.Ch7Rest.Marl76.isCCE_of_isNE_of_prob_eq G σ π hπ hNE,
    StatisticalRL.Ch7Rest.Marl76.coordGame, StatisticalRL.Ch7Rest.Marl76.coordPolicy,
    StatisticalRL.Ch7Rest.Marl76.coordGame_reward_mem,
    StatisticalRL.Ch7Rest.Marl76.coordPolicy_isCCE,
    StatisticalRL.Ch7Rest.Marl76.coordPolicy_not_product⟩

end MarlEquilibriaProofs

section ConvexDistanceTVProofs

/-- `Eq_convex_distance_le_TV` from the library export `convexDistance_le_tv` (namespace
`TDInference`), which holds on `ι → ℝ` for any finite `ι`; here `ι = Fin d`. -/
theorem Eq_convex_distance_le_TV_holds : Eq_convex_distance_le_TV := by
  intro d P Q hP hQ
  exact StatisticalRL.Ch7Rest.TDInference.convexDistance_le_tv P Q

end ConvexDistanceTVProofs

section TDWeightsProofs

/-- `Eq_tdWeights_sum` from the library exports `pluginWeight_eq` and `sum_pluginWeight`
(namespace `TDInference`; `pluginWeight T t` unfolds to `(t + 1) / ∑_u (u + 1)`). -/
theorem Eq_tdWeights_sum_holds : Eq_tdWeights_sum := fun T hT =>
  ⟨fun t => StatisticalRL.Ch7Rest.TDInference.pluginWeight_eq T t,
    StatisticalRL.Ch7Rest.TDInference.sum_pluginWeight hT⟩

end TDWeightsProofs

end StatisticalRL.Statements.Ch7
