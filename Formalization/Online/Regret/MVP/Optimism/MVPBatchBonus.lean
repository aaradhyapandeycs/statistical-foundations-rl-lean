import Formalization.Online.Regret.MVP.Optimism.MVPBatchFuture
import Formalization.Online.SourceOptimism.SourceBonusCompatibleBernstein
import Formalization.Online.SourceOptimism.VisitPrefixConcentrationUnion

/-! Fixed true-continuation bonus certificates for all deterministic MVP
batch slices under the actual expanded product law. No random-count iid claim. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance mvpBatchBonusStateMeasurable : MeasurableSpace State := ⊤

/-- The fixed-row, fixed-batch source bonus certificate, uniformly in U. -/
noncomputable def mvpBatchBonusGood {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (V : (Fin H × State × Action) → State → ℝ) (K : ℕ) (δ c₁ c₂ : ℝ)
    (r : Fin H × State × Action) (n : ℕ) : Set (Samples State Action H K) := by
  classical
  exact if hn : 0<n ∧ 2*n ≤ K then
    {data | ∀ U : State → ℝ, (∀ x, V r x ≤ U x ∧ U x ≤ H) →
      ((E r.1).transition r.2.1 r.2.2).expectation (V r) ≤
        (FiniteDistribution.empiricalRow n hn.1 (mvpBatchSlice K n hn.2
          (fun i => data ((r.1,r.2.1,r.2.2),i)))).expectation U +
        c₁ * Real.sqrt ((FiniteDistribution.empiricalRow n hn.1 (mvpBatchSlice K n hn.2
          (fun i => data ((r.1,r.2.1,r.2.2),i)))).variance U * (Real.log (1/δ)/n)) +
        c₂ * H * (Real.log (1/δ)/n)}
  else Set.univ

/-- The fixed batch confidence follows by mapping the actual joint product law
to its exact contiguous iid row-batch law. -/
theorem mvpBatchBonusGood_probability {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (hH : 0<H) (V : (Fin H × State × Action) → State → ℝ) (K : ℕ)
    (δ c₁ c₂ : ℝ) (hδ : 0<δ) (hδsmall : δ≤2/5)
    (hc₁ : 4≤c₁) (hc₂ : c₁^2≤c₂)
    (hV : ∀ r x, V r x ∈ Set.Icc (0:ℝ) H)
    (r : Fin H × State × Action) (n : ℕ) (hn : 0<n) (hfit : 2*n≤K) :
    1-2*δ ≤ (samplingLaw E K).real (mvpBatchBonusGood E V K δ c₁ c₂ r n) := by
  classical
  let d := (E r.1).transition r.2.1 r.2.2
  let draw : Samples State Action H K → Fin n → State := fun data =>
    mvpBatchSlice K n hfit (fun i => data ((r.1,r.2.1,r.2.2),i))
  let good : Set (Fin n → State) := {data | ∀ U : State → ℝ,
    (∀ x,V r x≤U x ∧ U x≤H) → d.expectation (V r) ≤
      (FiniteDistribution.empiricalRow n hn data).expectation U +
      c₁*Real.sqrt ((FiniteDistribution.empiricalRow n hn data).variance U*(Real.log (1/δ)/n))+
      c₂*H*(Real.log (1/δ)/n)}
  have hf := onlineFixedPrefix_source_bonus_confidence d (V r) n hn H δ c₁ c₂
    (by exact_mod_cast hH) hδ hδsmall hc₁ hc₂ (hV r)
  have heq : (samplingLaw E K).real (draw ⁻¹' good) = (d.sampleMeasure n).real good := by
    rw [measureReal_def, ← Measure.map_apply (measurable_of_countable draw)
      ((Set.to_countable good).measurableSet), mvp_batch_expanded_law E K n hfit r.1 r.2.1 r.2.2]
    rfl
  simp only [mvpBatchBonusGood, dif_pos (show 0<n ∧ 2*n ≤ K from ⟨hn,hfit⟩)]
  change 1-2*δ ≤ (samplingLaw E K).real (draw ⁻¹' good)
  rw [heq]
  exact hf

/-- One common product experiment controls every row and every feasible
nontrivial deterministic batch size, with the source factor 2·SAH·K. -/
theorem mvp_allBatchBonusGood_probability {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (hH : 0<H) (K : ℕ) (hK : 0<K)
    (V : (Fin H × State × Action) → State → ℝ) (δ c₁ c₂ : ℝ)
    (hδ : 0<δ) (hδsmall : δ≤2/5) (hc₁ : 4≤c₁) (hc₂ : c₁^2≤c₂)
    (hV : ∀ r x,V r x∈Set.Icc (0:ℝ) H) :
    1-2*(Fintype.card (Fin H × State × Action) : ℝ)*K*δ <
      (samplingLaw E K).real {data | ∀ r n, 3≤n → n<K → data ∈ mvpBatchBonusGood E V K δ c₁ c₂ r n} := by
  classical
  letI : Nonempty (Fin H) := ⟨⟨0,hH⟩⟩
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  apply onlineFixedPrefix_union_strict (samplingLaw E K) K hK δ hδ (mvpBatchBonusGood E V K δ c₁ c₂)
  intro r n hn hnK
  by_cases hfit : 2*n ≤ K
  · have hg := mvpBatchBonusGood_probability E hH V K δ c₁ c₂ hδ hδsmall hc₁ hc₂ hV r n (by omega) hfit
    have hc := measureReal_compl (μ := samplingLaw E K)
      ((Set.to_countable (mvpBatchBonusGood E V K δ c₁ c₂ r n)).measurableSet)
    rw [probReal_univ] at hc
    linarith
  · simp [mvpBatchBonusGood, hfit, le_of_lt hδ]
end StatisticalRL.FiniteHorizonGenerative
