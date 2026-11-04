import Formalization.ModelFree.TDSourceFullAccuracyUniversal
import Formalization.ModelFree.TDSourceSamplingProjection

/-! The TD accuracy theorem on the source's exact-T sampling experiment.
The concentration proof uses a padded array internally. The joint-law
projection and pathwise output equality remove that unused coordinate here. -/

open MeasureTheory
namespace StatisticalRL.TemporalDifference

local instance tdExactAccuracyStateMeasurable (State : Type*) :
    MeasurableSpace State := ⊤

/-- Theorem 4.1, `thm:policy-evaluation-TD`,
`chapters/generative_model_model_free.tex:179–224`, under exactly T independent
policy-row draws per state. All constants precede the model and accuracy inputs. -/
theorem tdSource_policyEvaluation_exactSamples_accuracy_exists_universal_constants :
    ∃ c₁ c₂ c₃ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ c₁ ≤ 1 ∧ 0 < c₃ ∧
    ∀ (State : Type*) (Action : Type*) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
      (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ),
      1 / 2 ≤ M.discount → 2 ≤ T →
      0 < δ → δ < 1 → 0 < ε → ε ≤ M.effectiveHorizon →
      tdSourceRateSchedule M.discount c₁ c₂ T η →
      ∀ (V₀ : State → ℝ),
      (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon) →
      c₃ * Real.log (T : ℝ) ^ 3 *
        Real.log ((Fintype.card State : ℝ) * T / δ) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ) →
      1 - δ ≤ (tdSourceSamplingLaw M π T).real
        {data | ∀ s : State,
          |tdSourceSampledIterate M π η T V₀ data s -
            M.trajectoryExpectedValue π s| ≤ ε} := by
  obtain ⟨c₁, c₂, c₃, hc₂, horder, hc₁, hc₃, hmain⟩ :=
    tdSource_policyEvaluation_accuracy_exists_universal_constants
  refine ⟨c₁, c₂, c₃, hc₂, horder, hc₁, hc₃, ?_⟩
  intro State Action _ _ M π η δ ε T hγ hT hδ hδone hε hεmax
    hη V₀ h₀ hbudget
  have hp := hmain State Action M π η δ ε T hγ hT hδ hδone
    hε hεmax hη V₀ h₀ hbudget
  let sourceGood : Set (TDSourceSamples State T) := {data | ∀ s : State,
    |tdSourceSampledIterate M π η T V₀ data s -
      M.trajectoryExpectedValue π s| ≤ ε}
  have hprojection : Measurable (tdUsedSampleProjection (State := State) T) :=
    measurable_of_countable _
  have hgood : MeasurableSet sourceGood := (Set.to_countable sourceGood).measurableSet
  have hprobability : (tdSourceSamplingLaw M π T).real sourceGood =
      (tdSamplingLaw M π T).real
        ((tdUsedSampleProjection T) ⁻¹' sourceGood) := by
    change ((tdSourceSamplingLaw M π T) sourceGood).toReal =
      ((tdSamplingLaw M π T) ((tdUsedSampleProjection T) ⁻¹' sourceGood)).toReal
    rw [← tdUsedSampleProjection_map_law M π T,
      Measure.map_apply hprojection hgood]
  change 1 - δ ≤ (tdSourceSamplingLaw M π T).real sourceGood
  rw [hprobability]
  refine hp.trans (measureReal_mono ?_)
  intro data hd
  change ∀ s : State,
    |tdSourceSampledIterate M π η T V₀ (tdUsedSampleProjection T data) s -
      M.trajectoryExpectedValue π s| ≤ ε
  intro s
  have hs := hd s
  change |tdSampledIterate M π η T V₀ data s -
    M.trajectoryExpectedValue π s| ≤ ε at hs
  rw [tdSampledIterate_eq_sourceSampledIterate M π η T V₀ data] at hs
  exact hs

end StatisticalRL.TemporalDifference
