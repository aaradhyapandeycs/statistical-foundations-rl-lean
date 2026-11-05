import Formalization.OfflineRL.EmittedLaw
import Formalization.OfflineRL.SampleSplitCorrectedProof

/-! Actual-law offline sample-splitting count bound.

The result applies to iid triples with the source joint law and derives the
row-projection law. No count event or transition-correctness certificate is an
input. The stated sample-size domain is `N ≥ 2`; see
`docs/SOURCE-ISSUES.md#C19`. -/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineRL.SampleSplitActual

open StatisticalRL StatisticalRL.OfflineRL

variable {State Action : Type*} [Fintype State] [Fintype Action]
  [Nonempty State] [Nonempty Action]

/-- Row projection of an observation sequence. -/
def rowLabels {N : ℕ} (x : Fin N → (State × Action) × State) : Fin N → State × Action :=
  fun i => (x i).1

/-- **Law form.** Any random sequence of `N ≥ 2` observations whose law is `N`
iid copies of the actual joint row/next-state law has row labels in the exact
corrected count event with probability `> 1 - δ`. -/
theorem sampleSplit_count_lower_of_jointLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : FiniteDistribution (State × Action))
    (P : State → Action → FiniteDistribution State) (N : ℕ) (hN : 2 ≤ N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    letI : MeasurableSpace (State × Action) := ⊤
    letI : MeasurableSpace ((State × Action) × State) := ⊤
    ∀ X : Ω → Fin N → (State × Action) × State, Measurable X →
      μ.map X = (JointRow.jointRow ρ P).sampleMeasure N →
      1 - δ < μ.real {ω | rowLabels (X ω) ∈ sampleSplitCountLowerEvent ρ.rowMeasure N δ} := by
  letI : MeasurableSpace (State × Action) := ⊤
  letI : MeasurableSpace ((State × Action) × State) := ⊤
  intro X hX hlaw
  classical
  haveI : IsProbabilityMeasure ρ.rowMeasure := by
    unfold FiniteDistribution.rowMeasure
    exact @PMF.toMeasure.isProbabilityMeasure _ ⊤ ρ.toPMF
  have hrow : Measurable (rowLabels (State := State) (Action := Action) (N := N)) :=
    measurable_of_countable _
  have hE : MeasurableSet (sampleSplitCountLowerEvent ρ.rowMeasure N δ) :=
    (Set.to_countable _).measurableSet
  have hmap : μ.map (fun ω => rowLabels (X ω)) = Measure.pi (fun _ : Fin N => ρ.rowMeasure) := by
    have hc : (fun ω => rowLabels (X ω)) = rowLabels ∘ X := rfl
    rw [hc, ← Measure.map_map hrow hX, hlaw]
    exact JointRow.jointRow_sample_projection ρ P N
  have hset : {ω | rowLabels (X ω) ∈ sampleSplitCountLowerEvent ρ.rowMeasure N δ} =
      (fun ω => rowLabels (X ω)) ⁻¹' sampleSplitCountLowerEvent ρ.rowMeasure N δ := rfl
  rw [hset, ← map_measureReal_apply (f := fun ω => rowLabels (X ω)) (hrow.comp hX) hE, hmap]
  exact sampleSplit_count_lower_corrected_holds ρ.rowMeasure N hN δ hδ hδ1

variable [DecidableEq State] [DecidableEq Action]

/-- **Actual emitted data.** For iid behaviour labels and an independent
transition stack, the row labels of the emitted observations satisfy
the exact corrected count event with probability `> 1 - δ`, for `N ≥ 2`. -/
theorem sampleSplit_count_lower_emitted
    (ρ : FiniteDistribution (State × Action))
    (P : State → Action → FiniteDistribution State) (N : ℕ) (hN : 2 ≤ N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    letI : MeasurableSpace State := ⊤
    letI : MeasurableSpace (State × Action) := ⊤
    1 - δ < ((ρ.sampleMeasure N).prod (EmittedLaw.transitionStack P N)).real
      {ω | rowLabels (EmittedLaw.emitObservation ω) ∈
        sampleSplitCountLowerEvent ρ.rowMeasure N δ} := by
  letI : MeasurableSpace State := ⊤
  letI : MeasurableSpace (State × Action) := ⊤
  letI : MeasurableSpace ((State × Action) × State) := ⊤
  haveI : IsProbabilityMeasure (EmittedLaw.transitionStack P N) := by
    haveI : ∀ r : State × Action, IsProbabilityMeasure (P r.1 r.2).rowMeasure := fun r => by
      unfold FiniteDistribution.rowMeasure
      exact @PMF.toMeasure.isProbabilityMeasure _ ⊤ (P r.1 r.2).toPMF
    show IsProbabilityMeasure (Measure.pi _); infer_instance
  haveI : IsProbabilityMeasure (ρ.sampleMeasure N) := by
    haveI : IsProbabilityMeasure ρ.rowMeasure := by
      unfold FiniteDistribution.rowMeasure
      exact @PMF.toMeasure.isProbabilityMeasure _ ⊤ ρ.toPMF
    unfold FiniteDistribution.sampleMeasure; infer_instance
  exact sampleSplit_count_lower_of_jointLaw _ ρ P N hN δ hδ hδ1
    EmittedLaw.emitObservation (measurable_of_countable _) (EmittedLaw.emitObservation_law ρ P N)

end StatisticalRL.OfflineRL.SampleSplitActual
