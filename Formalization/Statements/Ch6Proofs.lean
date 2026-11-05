import Formalization.Statements.Ch6
import Formalization.OfflineRL.LCBFallbackApplication
import Formalization.OfflineRL.MonotoneContractionCorrected
import Formalization.OfflineRL.SampleSplitActual
import Formalization.OfflineRL.PreliminaryFacts

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

end StatisticalRL.Statements.Ch6
