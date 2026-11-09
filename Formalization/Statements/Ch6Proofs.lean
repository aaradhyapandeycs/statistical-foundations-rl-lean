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
import Formalization.OfflineRL.LowerBoundRandomized
import Formalization.OfflineRL.BernsteinInfiniteData
import Formalization.OfflineRL.VILCBTheorem
import Formalization.OfflineRL.FiniteVILCB.Theorem
import Formalization.OfflineRL.FiniteVILCB.LibraryBridge
import Formalization.OfflineRL.FiniteLCBQ.Export
import Formalization.OfflineRL.ConcentrabilityFacts
import Formalization.OfflineRL.VILCBIterationCount
import Formalization.OfflineRL.BanditExample

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
  intro S A _ _ M π ρ V b hγ hV0 hV1 hb hres
  exact StatisticalRL.OfflineRL.BonusSummation.occupancyWeightedVariance_mdp M
    π ρ V b hγ hV0 hV1 hb hres

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

/-- Apply the library export `offline_minimax_lower_bound_randomized`; no new proof. -/
theorem Thm6_13_randomized_holds.{u} : Thm6_13_randomized.{u} :=
  StatisticalRL.OfflineRL.LowerBound.offline_minimax_lower_bound_randomized.{u}

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
theorem Lemma6_9_restricted_holds : Lemma6_9_restricted.{u, v, w} := by
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

section VILCBTheorem

universe u v w

/-- Apply the library export `vilcb_infinite_offline` with `c_b₀ = 96` and `c₁ = 10⁴ c_b`;
no new proof. -/
theorem Thm6_3_holds : Thm6_3.{u, v, w} :=
  ⟨96, by norm_num, fun cb hcb => ⟨10000 * cb, by positivity,
    fun S A _ _ _ _ M db p hγ hr hpcb hhalf τmax hτ ρ πstar hopt ε hε hε1 hC hN Ω _ μ _ =>
      StatisticalRL.OfflineVILCB.Theorem63.vilcb_infinite_offline cb hcb S A M db p hγ hr hpcb
        hhalf τmax hτ ρ πstar hopt ε hε hε1 hC hN Ω μ⟩⟩

end VILCBTheorem

section FiniteVILCBTheorem

universe u v w

/-- Apply the library export `FiniteVILCB.finite_vilcb_restricted` with `c_b₀ = 16` and
`c_k = 69120 c_b`, through the library bridges (`isOptimal_of_optimal`,
`concentrability_eq_library`, `gap_bridge`); no new proof of the result. -/
theorem Thm6_16_restricted_holds : Thm6_16_restricted.{u, v, w} := by
  refine ⟨16, by norm_num, fun cb hcb ↦ ⟨69120 * cb, by linarith, ?_⟩⟩
  intro S A _ _ _ _ H hH E πb ρb ρ πs hopt ε δ hε hεH hδ hδ1 K hK Cstar hC hKc Ω _ μ _ X hX hind
    hlaw
  have hconc : Cstar = FiniteVILCB.concentrability E πb ρb ρ πs :=
    (FiniteVILCB.concentrability_eq_library E πb ρb ρ πs).symm
  rw [hconc] at hC hKc
  have h := FiniteVILCB.finite_vilcb_restricted H hH E πb ρb ρ πs
    (FiniteVILCB.isOptimal_of_optimal E πs hopt) cb hcb ε δ hε hεH hδ hδ1 K hK hC hKc μ X hX hind
    hlaw
  simp only [FiniteVILCB.gap_bridge] at h
  exact h

end FiniteVILCBTheorem

section FiniteLCBQTheorem

universe u v w

/-- Apply the library export `LCBQFinite.lcbqFinite_restricted` with `c_b₀ = 5` and
`c_a = 10⁶ c_b²`, through the library bridges (`isOptimal_of_optimal`,
`concentrability_eq_library`, `gap_bridge`). The export assumes the L-form size condition; the
library lemma `LCBQFinite.printed_size_imp_export_size` derives it (or `|A| = 1`) from the printed
`log³` condition and `L ≤ max(ι, ι³)`. No new proof of the result. -/
theorem Thm6_17_restricted_holds : Thm6_17_restricted.{u, v, w} := by
  refine ⟨5, by norm_num, fun cb hcb ↦ ⟨10 ^ 6 * cb ^ 2, by
    have : 0 < cb := by linarith
    positivity, ?_⟩⟩
  intro S A _ _ _ _ H hH E πb ρb ρ πs hopt ε δ hε hεH hδ hδ1 K hK L hL hL3 sel hsel π₀ Cstar hC
    hKc Ω _ μ _ X hX hind hlaw
  have hconc : Cstar = FiniteVILCB.concentrability E πb ρb ρ πs :=
    (FiniteVILCB.concentrability_eq_library E πb ρb ρ πs).symm
  rw [hconc] at hC hKc
  have h := LCBQFinite.lcbqFinite_restricted cb hcb H hH E πb ρb ρ πs
    (FiniteVILCB.isOptimal_of_optimal E πs hopt) ε δ hε hεH hδ hδ1 K hK L hL sel hsel π₀ hC
    (LCBQFinite.printed_size_imp_export_size cb hcb H hH E πb ρb ρ πs hC ε δ hε hεH hδ hδ1 K hK L hL3
      hKc) μ X hX hind hlaw
  simp only [FiniteVILCB.gap_bridge] at h
  exact h

end FiniteLCBQTheorem

section TrivialBatchA

/-- Apply `iSup_pointMass_ratio`. -/
theorem Eq_defn_Cstar_bandits_holds : Eq_defn_Cstar_bandits := by
  intro Arm _ _ _ d aStar
  exact StatisticalRL.OfflineRL.Concentrability.iSup_pointMass_ratio d aStar

/-- Apply `exampleDesign_cstar` and `tendsto_div_sub_one`. -/
theorem Remark6_4_holds : Remark6_4 :=
  ⟨fun _ hN ↦ StatisticalRL.OfflineRL.exampleDesign_cstar hN,
    StatisticalRL.OfflineRL.tendsto_div_sub_one⟩

/-- Apply `DiscountedMDP.cstar_ge_one`. -/
theorem Remark6_2_holds : Remark6_2 := by
  intro S A _ _ M π ρ db
  exact M.cstar_ge_one π ρ db

/-- Apply `cstarClipped_le_cstar`, `exists_cstarClipped_eq_inv_card` and
`cstarClipped_ge_inv_card`. -/
theorem Remark6_3_holds : Remark6_3 :=
  ⟨fun _ _ _ _ M π ρ db ↦ M.cstarClipped_le_cstar π ρ db,
    fun S A _ _ _ _ ↦ StatisticalRL.DiscountedMDP.exists_cstarClipped_eq_inv_card S A,
    fun _ _ _ _ M π ρ db ↦ M.cstarClipped_ge_inv_card π ρ db⟩

/-- Apply `Input.iter_iterationCount_restricted`. -/
theorem Lemma6_2_iterationCount_restricted_holds : Lemma6_2_iterationCount_restricted := by
  intro S A _ _ M _ hγ
  exact M.iter_iterationCount_restricted hγ

/-- Apply `exampleDesign_lcb_selects_optimal`. -/
theorem Remark6_5_holds : Remark6_5 := by
  intro N δ hN hδ hδ1 hlarge
  exact StatisticalRL.OfflineRL.exampleDesign_lcb_selects_optimal N δ hN hδ hδ1 hlarge

/-- Apply `exampleDesign_empiricalBest_regret`. -/
theorem Example6_1_holds : Example6_1 := by
  intro N hN _ _ sel hsel
  exact StatisticalRL.OfflineRL.exampleDesign_empiricalBest_regret N hN sel hsel

end TrivialBatchA

end StatisticalRL.Statements.Ch6
