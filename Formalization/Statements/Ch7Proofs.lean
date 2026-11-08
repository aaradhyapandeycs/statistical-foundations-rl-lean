import Formalization.Statements.Ch7
import Formalization.RobustRL.TVSourceMaximum
import Formalization.RobustRL.ChiSquaredSourceMaximum
import Formalization.Ch7Rest.LowerBound710
import Formalization.RobustRL.Ch7.LowerBound73
import Formalization.RobustRL.Ch7.LowerBound75
import Formalization.Ch7Rest.Marl78Main
import Formalization.Ch7Rest.FedSync79Main

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


/-- `Thm7_10` from `lowerBound_of_fewRounds_onRange` with `c₀ = 1`, `C_γ = lbConst 1 γ`. -/
theorem Thm7_10_holds : Thm7_10 := by
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

end StatisticalRL.Statements.Ch7
