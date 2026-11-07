import Formalization.Statements.Ch6
import Formalization.OfflineRL.LCBQMartingale
import Formalization.OfflineRL.LCBQLemma612
import Formalization.OfflineRL.LCBQDecomposition
import Formalization.OfflineRL.LCBQUsefulSeries
import Formalization.OfflineRL.LowerBoundFamilyKL
import Formalization.OfflineRL.LowerBoundFamilyValues
import Formalization.OfflineRL.OccupancyWeightedVarianceMDP
import Formalization.OfflineRL.LCBFallbackApplication
import Formalization.OfflineRL.MonotoneContractionCorrected
import Formalization.OfflineRL.SampleSplitActual
import Formalization.OfflineRL.PreliminaryFacts
import Formalization.OfflineRL.LowerBoundMinimax
import Formalization.OfflineRL.BernsteinInfiniteData

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.Statements.Ch6

/-- Apply the reviewed probability theorem; no new proof or extra premise. -/
theorem Thm6_1_zeroCountFallback_corrected_holds : Thm6_1_zeroCountFallback_corrected := by
  intro Arm _ _ _ _ d _ r hr0 hr1 aStar hopt hd N δ hδ hδ1 hN
  exact StatisticalRL.OfflineRL.lcbFallback_regret_probability d r hr0 hr1 aStar hopt hd N δ hδ hδ1 hN

/-- Apply the corrected-Lemma-6.2 export; no new proof. -/
theorem Lemma6_2_corrected_holds : Lemma6_2_corrected := by
  intro S A _ _ M _ hγ
  exact M.lem_monotone_contraction_corrected hγ


section SampleSplitCorrected

theorem Lemma6_5_sampleSplit_actualData_corrected_holds :
    Lemma6_5_sampleSplit_actualData_corrected := by
  intro State Action _ _ _ _ ρ P Ω _ μ _ N hN δ hδ hδ1
  letI : MeasurableSpace (State × Action) := ⊤
  letI : MeasurableSpace ((State × Action) × State) := ⊤
  intro X hX hind hmarg
  classical
  -- Identify the source triple law with the proved joint-row law.
  have hrow : (∑ t : (State × Action) × State,
      ENNReal.ofReal (ρ.prob t.1 * (P t.1.1 t.1.2).prob t.2) • Measure.dirac t) =
      (OfflineRL.JointRow.jointRow ρ P).rowMeasure := by
    refine Measure.ext_iff_singleton.2 fun x => ?_
    rw [Measure.finset_sum_apply]
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton x), Set.indicator_apply,
      Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ x, if_pos (Finset.mem_univ x)]
    unfold FiniteDistribution.rowMeasure
    rw [@PMF.toMeasure_apply_singleton _ ⊤ _ x MeasurableSpace.measurableSet_top]
    unfold FiniteDistribution.toPMF
    rw [PMF.ofFintype_apply]
    rfl
  have hlaw : μ.map X = (OfflineRL.JointRow.jointRow ρ P).sampleMeasure N := by
    have h := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (measurable_pi_apply i).comp hX |>.aemeasurable)).1 hind
    simp only [Function.comp_def] at h
    calc μ.map X = μ.map (fun ω i => X ω i) := rfl
      _ = Measure.pi (fun i => μ.map (fun ω => X ω i)) := h
      _ = (OfflineRL.JointRow.jointRow ρ P).sampleMeasure N := by
        unfold FiniteDistribution.sampleMeasure
        congr 1
        funext i
        rw [hmarg i, hrow]
  have hmain := OfflineRL.SampleSplitActual.sampleSplit_count_lower_of_jointLaw μ ρ P N hN δ hδ hδ1
    X hX hlaw
  convert hmain using 3 with ω
  funext ω
  simp only [OfflineRL.sampleSplitCountLowerEvent, Set.mem_setOf_eq]
  apply propext
  refine forall_congr' fun sa => ?_
  have hmass : ρ.rowMeasure.real {sa} = ρ.prob sa := by
    unfold Measure.real FiniteDistribution.rowMeasure
    rw [@PMF.toMeasure_apply_singleton _ ⊤ _ sa MeasurableSpace.measurableSet_top]
    unfold FiniteDistribution.toPMF
    rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (ρ.prob_nonneg sa)]
  have hcount : ((OfflineRL.visitCount (fun i (x : Fin N → State × Action) => x i) sa
      (OfflineRL.SampleSplitActual.rowLabels (X ω)) : ℕ) : ℝ) =
      (((Finset.univ.filter fun i : Fin N => (X ω i).1 = sa).card : ℕ) : ℝ) := by
    unfold OfflineRL.visitCount OfflineRL.SampleSplitActual.rowLabels
    rw [Finset.card_filter]
  rw [hmass, hcount]

end SampleSplitCorrected


/-- Apply the actual VI-LCB consumer; the statement index adds no premise. -/
theorem Lemma6_4_holds : Lemma6_4 := by
  intro S A _ _ M _ hγ τ hτ
  exact M.exists_fixed_point_preliminary_facts hγ τ hτ

theorem Lemma6_7_restricted_holds : Lemma6_7_restricted := by
  intro S A _ _ M ρ V b hγ hV0 hV1 hb hres
  exact StatisticalRL.OfflineRL.BonusSummation.occupancyWeightedVariance_mdp M
    M.optimalGreedyPolicy ρ V b hγ hV0 hV1 hb hres

theorem Lemma6_14_restricted_holds : Lemma6_14_restricted := by
  intro m hm γ ε C hγ hγ1 hε hεmax hC θ
  exact StatisticalRL.OfflineRL.LowerBound.lb_value_policy m hm γ ε C hγ hγ1 hε hεmax hC θ

theorem Lemma6_15_holds : Lemma6_15 :=
  ⟨16 * 336 ^ 2, by norm_num, fun m hm γ ε C hγ hγ1 hε hεmax hC θ θ' i a =>
    StatisticalRL.OfflineRL.LowerBound.lb_transition_kl m hm γ ε C hγ hγ1 hε hεmax hC θ θ' i a⟩

theorem Lemma6_11_restricted_holds : Lemma6_11_restricted :=
  ⟨84, by norm_num, fun S A _ _ M ρ δ T W hδ hδ1 hT hι hW =>
    StatisticalRL.OfflineRL.LCBQ.lcbq_useful M M.optimalGreedyPolicy ρ δ T W hδ hδ1 hT hι hW⟩

/-- Apply the library theorem `offline_minimax_lower_bound`; no new proof. -/
theorem Thm6_13_holds : Thm6_13 :=
  StatisticalRL.OfflineRL.LowerBound.offline_minimax_lower_bound

section BernsteinInfinite

universe u v w

/-- Apply the Lemma 6.18 library export; the strict bound is weakened to the printed `≥`. -/
theorem Lemma6_18_holds : Lemma6_18.{u, v} := by
  intro S _ Ω _ μ _ d γ _ hγ1 δ hδ hδ8 n hn
  letI : MeasurableSpace S := ⊤
  intro draw hdraw hlaw V hV hindep hrange
  exact (StatisticalRL.OfflineVILCB.BernsteinInfinite.bernsteinInfinite_fixedRow μ d γ hγ1 δ hδ hδ8
    n hn draw hdraw hlaw V hV hindep hrange).le

/-- Apply the Lemma 6.6 library export with the event level set to the penalty's `δ`. -/
theorem Lemma6_6_holds : Lemma6_6.{u, v, w} := by
  intro S A _ _ _ _ ρ P p hγ Ω _ μ _
  letI : MeasurableSpace ((S × A) × S) := ⊤
  intro X hX hind hmarg
  exact StatisticalRL.OfflineVILCB.LeaveOneOut.bernsteinInfinite_iid p hγ ρ P μ p.δ p.δ_pos
    p.δ_lt_one X hX hind hmarg

end BernsteinInfinite


section LCBQ

universe u v w

/-- Apply the library export `lemma69_prob` (with `c_b₀ = 4`); no new proof. -/
theorem Lemma6_9_holds : Lemma6_9.{u, v, w} := by
  refine ⟨4, by norm_num, fun cb hcb S A _ _ M db sel _ π₀ T δ hδ hδ1 Ω _ μ _ => ?_⟩
  intro X hX hind hmarg
  have h := OfflineRL.LCBQ.lemma69_prob M cb δ sel π₀ hcb db T hδ hδ1 μ X hX hind hmarg
  refine h.le.trans (measureReal_mono ?_)
  intro ω hω t ht1 htT s a
  exact ⟨hω.1 t ht1 htT s a, hω.2 t ht1 htT s a⟩

/-- Apply the library export `lemma610_prob` (with `c_b₀ = 4`); no new proof. -/
theorem Lemma6_10_restricted_holds : Lemma6_10_restricted.{u, v, w} := by
  refine ⟨4, by norm_num, fun cb hcb S A _ _ M db sel hsel π₀ T δ hδ hδ1 Ω _ μ _ => ?_⟩
  intro X hX hind hmarg
  exact OfflineRL.LCBQ.lemma610_prob M cb δ sel π₀ hcb hsel db T hδ hδ1 μ X hX hind hmarg

/-- Apply the library export `lemma612_prob` (`c_b₀ = 4`, `C = lemma612Const c_b`); no new
proof. -/
theorem Lemma6_12_restricted_holds : Lemma6_12_restricted.{u, v, w} := by
  refine ⟨4, by norm_num, fun cb hcb => ⟨OfflineRL.LCBQ.lemma612Const cb, by
    unfold OfflineRL.LCBQ.lemma612Const; linarith,
    fun S A _ _ M db sel _ π₀ T δ hδ hδ1 ρ πstar _ hι Ω _ μ _ => ?_⟩⟩
  intro X hX hind hmarg
  exact OfflineRL.LCBQ.lemma612_prob M cb δ sel π₀ ρ πstar db hcb T hδ hδ1 hι μ X hX hind hmarg

/-- Apply the library export `thm68_corrected_prob` (`c_b₀ = 4`, `c₂ = thm68Const c_b`); no new
proof. -/
theorem Thm6_8_corrected_holds : Thm6_8_corrected.{u, v, w} := by
  refine ⟨4, by norm_num, fun cb hcb => ⟨OfflineRL.LCBQ.thm68Const cb, by
    unfold OfflineRL.LCBQ.thm68Const OfflineRL.LCBQ.lemma612Const; positivity,
    fun S A _ _ M db sel hsel π₀ T δ hδ hδ1 hT ρ πstar hopt ε hε hεx hCs hcond Ω _ μ _ => ?_⟩⟩
  intro X hX hind hmarg
  exact OfflineRL.LCBQ.thm68_corrected_prob M cb δ sel π₀ ρ πstar db hcb hsel hopt T hT hδ hδ1 hCs
    ε hε hεx hcond μ X hX hind hmarg

end LCBQ

end StatisticalRL.Statements.Ch6
