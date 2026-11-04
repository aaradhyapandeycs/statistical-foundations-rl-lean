import Formalization.Online.Regret.W2.OnlineW2CoordinateStack

/-! Pullback of fixed-coordinate stack certificates to the actual observed
pre-episode history and then to the direct sequential source law. No adaptive
count is conditioned upon as iid. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w2ObservedStateMeasurable : MeasurableSpace State := ⊤
local instance w2ObservedTranscriptMeasurable (H K : ℕ) :
    MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤
local instance w2ObservedAtomMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤
noncomputable local instance w2ObservedStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w2ObservedActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The actual observed empirical row obeys every coordinate certificate at
pre-episode counts at least three. -/
noncomputable def onlineObservedW2CoordinateCertificates
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action) (δ : ℝ)
    (history : List (OnlineMDPRow State Action H × State)) : Prop :=
  ∀ k : Fin K, ∀ r : OnlineMDPRow State Action H, ∀ x : State,
    ∀ hn : 3 ≤ (onlineRowOutcomes (history.take (k.val * H)) r).length,
      let n := (onlineRowOutcomes (history.take (k.val * H)) r).length
      let emp := FiniteDistribution.empiricalRow n (by omega)
        (onlineObservedRowData (history.take (k.val * H)) r)
      |emp.expectation (onlineW2Indicator x) -
        (onlineMDPSuccessorRowLaw E r).expectation (onlineW2Indicator x)| ≤
        onlineTrueW1Radius 1 δ n (onlineMDPSuccessorRowLaw E r) (onlineW2Indicator x)

/-- Every actual observed count selects a prefix whose certificate held
simultaneously before the path was selected. -/
theorem onlineW2StackGood_implies_observed
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (δ : ℝ)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (hgood : ∀ x r n, 3 ≤ n → n < K →
      data ∈ onlineW2CoordinateGood (onlineMDPSuccessorRowLaw E) K δ x r n) :
    onlineObservedW2CoordinateCertificates H K E δ
      (onlineStackHistory (onlineEpisodicChoose H K hH initial fallback planner)
        (onlineFiniteStackExtend K fallback data) (K * H)) := by
  intro k r x hn
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let stream := onlineFiniteStackExtend K fallback data
  have htake := onlineStackHistory_take choose stream (K * H) (k.val * H)
    (Nat.mul_le_mul_right H k.isLt.le)
  have hbound (hist : List (OnlineMDPRow State Action H × State))
      (heq : hist = onlineStackHistory choose stream (k.val * H))
      (hn' : 3 ≤ (onlineRowOutcomes hist r).length) :
      let n := (onlineRowOutcomes hist r).length
      let emp := FiniteDistribution.empiricalRow n (by omega) (onlineObservedRowData hist r)
      |emp.expectation (onlineW2Indicator x) -
        (onlineMDPSuccessorRowLaw E r).expectation (onlineW2Indicator x)| ≤
        onlineTrueW1Radius 1 δ n (onlineMDPSuccessorRowLaw E r) (onlineW2Indicator x) := by
    subst hist
    let history := onlineStackHistory choose stream (k.val * H)
    let n := (onlineRowOutcomes history r).length
    have hcount : n ≤ k.val := onlineActualStack_preEpisode_count_le H K hH initial
      fallback planner data k r
    have hnK : n < K := hcount.trans_lt k.isLt
    have hn3 : 3 ≤ n := hn'
    have hcert := hgood x r n hn3 hnK
    have hrow := onlineFiniteStack_empiricalRow_eq_prefix choose K (k.val * H) fallback
      data r hnK.le (by change 0 < n; omega)
    have hbounds : 3 ≤ n ∧ n < K := ⟨hn3, hnK⟩
    simp only [onlineW2CoordinateGood, onlineTrueW1StackPrefixGood, dif_pos hbounds,
      Set.mem_setOf_eq] at hcert
    dsimp only
    dsimp only [stream]
    rw [hrow]
    exact hcert
  exact hbound _ htake hn

/-- Direct sequential experiment has the same observed-coordinate event with
4·S·(SAH)·K·δ failure margin. -/
theorem onlineSequential_observedW2CoordinateCertificates_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5) :
    1 - 4 * (Fintype.card State : ℝ) * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        {sample | onlineObservedW2CoordinateCertificates H K E δ
          (onlineSequentialPathHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
            (K * H) [] sample.2)} := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  letI : Nonempty (Fin H) := ⟨⟨0, hH⟩⟩
  let μ := onlineMDPInitialStackLaw E ρ K
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, onlineMDPInitialStackLaw, onlineMDPStackLaw]
    infer_instance
  let ν := onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)
  let good := {data | ∀ x r n, 3 ≤ n → n < K →
    data ∈ onlineW2CoordinateGood (onlineMDPSuccessorRowLaw E) K δ x r n}
  let target : Set (OnlineResetTranscript State Action H K) :=
    {record | onlineObservedW2CoordinateCertificates H K E δ record.2}
  let observe := fun sample : (Fin K → State) × (OnlineMDPRow State Action H × Fin K → State) =>
    (sample.1, onlineStackHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
      (onlineFiniteStackExtend K fallback sample.2) (K * H))
  let encode := fun sample : (Fin K → State) × OnlineOutcomePath State (K * H) =>
    (sample.1, onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2)
  have hstack := onlineW2Stack_allCoordinatesPrefixes_strict (onlineMDPSuccessorRowLaw E)
    K hK δ hδ hδsmall
  have hlift : μ.real (Set.univ ×ˢ good) = (onlineMDPStackLaw E K).real good := by
    dsimp [μ, onlineMDPInitialStackLaw]
    rw [measureReal_def, Measure.prod_prod, measure_univ, one_mul]
    rfl
  have hsub : (Set.univ ×ˢ good) ⊆ observe ⁻¹' target := by
    intro sample hgood
    exact onlineW2StackGood_implies_observed H K hH E sample.1 fallback planner δ sample.2 hgood.2
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have hcouple : μ.map observe = ν.rowMeasure.map encode :=
    onlineStack_sequential_transcriptLaw_eq H K hH E ρ fallback planner (K * H) le_rfl
  have hprob : μ.real (observe ⁻¹' target) = ν.rowMeasure.real (encode ⁻¹' target) := by
    have h := congrArg (fun law : Measure (OnlineResetTranscript State Action H K) =>
      law.real target) hcouple
    simpa only [measureReal_def, Measure.map_apply (measurable_of_countable _)
      ((Set.to_countable target).measurableSet)] using h
  change 1 - 4 * (Fintype.card State : ℝ) * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ <
    ν.rowMeasure.real (encode ⁻¹' target)
  rw [← hprob]
  apply lt_of_lt_of_le _ (hlift.symm.le.trans hmono)
  simpa [good, onlineMDPStackLaw] using hstack
end StatisticalRL.OnlineRL
