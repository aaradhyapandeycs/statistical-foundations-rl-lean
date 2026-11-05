import Formalization.OfflineRL.OfflineCountChernoff

/-!
Corrected/restricted statement for the sample-splitting count event in
`offlineRL.tex`, source label `lem:sample-split-infinite`, lines 1104–1120.
This version explicitly adds `2 ≤ N`; the printed unrestricted endpoint is
not silently changed or claimed here. The original result remains open.
-/

open MeasureTheory

namespace StatisticalRL
namespace OfflineRL

/-- The simultaneous count lower-bound event from the source, with its
source constants and a positive-sample-size restriction. -/
noncomputable def sampleSplitCountLowerEvent
    {State Action : Type*} [Fintype State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    [MeasurableSpace (State × Action)] [MeasurableSingletonClass (State × Action)]
    (d : Measure (State × Action)) (N : ℕ) (δ : ℝ) :
    Set (Fin N → State × Action) := by
  classical
  exact {ω | ∀ sa : State × Action,
    max
      (visitCount (fun i (x : Fin N → State × Action) => x i) sa ω : ℝ)
      ((2 / 3 : ℝ) * Real.log ((Fintype.card State : ℝ) * N / δ))
      ≥ (N : ℝ) * d.real {sa} / 12}

/-- Restricted/corrected form of `lem:sample-split-infinite`
(`offlineRL.tex:1104–1120`): the iid state-action dataset has the displayed
simultaneous count property with strict probability, for `N ≥ 2`. The added
sample-size condition addresses the proof's union-bound endpoint; this is not
claimed to be the unrestricted printed statement. -/
def sampleSplit_count_lower_corrected : Prop :=
  ∀ {State Action : Type*} [Fintype State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    [MeasurableSpace (State × Action)] [MeasurableSingletonClass (State × Action)]
    (d : Measure (State × Action)) [IsProbabilityMeasure d]
    (N : ℕ) (hN : 2 ≤ N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1),
    1 - δ < (Measure.pi (fun _ : Fin N => d)).real
      (sampleSplitCountLowerEvent d N δ)

end OfflineRL
end StatisticalRL
