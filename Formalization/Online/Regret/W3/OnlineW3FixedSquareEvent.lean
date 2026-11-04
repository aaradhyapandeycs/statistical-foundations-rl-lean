import Formalization.Online.Regret.W1.OnlineW1TrueVariancePrefix

/-! Fixed true optimal squared-value certificate on the actual history. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w3SquareStateMeasurable : MeasurableSpace State := ⊤
local instance w3SquareTranscriptMeasurable (H K : ℕ) : MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤
local instance w3SquareAtomMeasurable (K n : ℕ) : MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤
noncomputable local instance w3SquareStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w3SquareActionDecidable : DecidableEq Action := Classical.decEq Action

noncomputable def onlineW3SquaredTrueFamily (H : ℕ) (E : Fin H → EnvironmentStage State Action)
    (r : OnlineMDPRow State Action H) (s : State) : ℝ := (onlineTrueSuffixRowFamily E r s)^2

theorem onlineW3SquaredTrueFamily_range (H : ℕ) (E : Fin H → EnvironmentStage State Action)
    (r : OnlineMDPRow State Action H) (s : State) : onlineW3SquaredTrueFamily H E r s ∈ Set.Icc 0 ((H : ℝ)^2) := by
  have h := onlineTrueSuffixRowFamily_range H E r s
  constructor
  · exact sq_nonneg _
  · dsimp [onlineW3SquaredTrueFamily]
    nlinarith [h.1, h.2, sq_nonneg ((H : ℝ) - onlineTrueSuffixRowFamily E r s)]

/-- Two-sided bounds at every actual completed-history row with count at
least three, for the same fixed true optimal continuation family. -/
noncomputable def onlineObservedW3SquareCertificates
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action) (δ : ℝ)
    (history : List (OnlineMDPRow State Action H × State)) : Prop :=
  ∀ k : Fin K, ∀ r : OnlineMDPRow State Action H,
    ∀ hn : 3 ≤ (onlineRowOutcomes (history.take (k.val * H)) r).length,
      let n := (onlineRowOutcomes (history.take (k.val * H)) r).length
      let emp := FiniteDistribution.empiricalRow n (by omega)
        (onlineObservedRowData (history.take (k.val * H)) r)
      let V := onlineW3SquaredTrueFamily H E r
      |emp.expectation V - (onlineMDPSuccessorRowLaw E r).expectation V| ≤
        onlineTrueW1Radius ((H : ℝ)^2) δ n (onlineMDPSuccessorRowLaw E r) V

/-- Simultaneous deterministic-prefix goodness implies the same bound at
actual observed row counts. -/
theorem onlineW3SquareStackGood_implies_observed
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (δ : ℝ)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (hgood : ∀ r n, 3 ≤ n → n < K →
      data ∈ onlineTrueW1StackPrefixGood (onlineMDPSuccessorRowLaw E)
        (onlineW3SquaredTrueFamily H E) K ((H : ℝ)^2) δ r n) :
    onlineObservedW3SquareCertificates H K E δ
      (onlineStackHistory (onlineEpisodicChoose H K hH initial fallback planner)
        (onlineFiniteStackExtend K fallback data) (K * H)) := by
  intro k r hn
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let stream := onlineFiniteStackExtend K fallback data
  have htake := onlineStackHistory_take choose stream (K * H) (k.val * H)
    (Nat.mul_le_mul_right H k.isLt.le)
  have hbound (hist : List (OnlineMDPRow State Action H × State))
      (heq : hist = onlineStackHistory choose stream (k.val * H))
      (hn' : 3 ≤ (onlineRowOutcomes hist r).length) :
      let n := (onlineRowOutcomes hist r).length
      let emp := FiniteDistribution.empiricalRow n (by omega) (onlineObservedRowData hist r)
      let V := onlineW3SquaredTrueFamily H E r
      |emp.expectation V - (onlineMDPSuccessorRowLaw E r).expectation V| ≤
        onlineTrueW1Radius ((H : ℝ)^2) δ n (onlineMDPSuccessorRowLaw E r) V := by
    subst hist
    let history := onlineStackHistory choose stream (k.val * H)
    let n := (onlineRowOutcomes history r).length
    have hcount : n ≤ k.val := onlineActualStack_preEpisode_count_le H K hH initial
      fallback planner data k r
    have hnK : n < K := hcount.trans_lt k.isLt
    have hn3 : 3 ≤ n := hn'
    have hcert := hgood r n hn3 hnK
    have hrow := onlineFiniteStack_empiricalRow_eq_prefix choose K (k.val * H) fallback
      data r hnK.le (by change 0 < n; omega)
    have hbounds : 3 ≤ n ∧ n < K := ⟨hn3, hnK⟩
    simp only [onlineTrueW1StackPrefixGood, dif_pos hbounds, Set.mem_setOf_eq] at hcert
    dsimp only
    dsimp only [stream]
    rw [hrow]
    exact hcert
  exact hbound _ htake hn

/-- Same sequential source law as the actual planner: all observed
positive-count squared-value W₃ row certificates hold simultaneously with the strict
factor-two finite-prefix confidence. -/
theorem onlineSequential_observedW3SquareCertificates_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5) :
    1 - 4 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        {sample | onlineObservedW3SquareCertificates H K E δ
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
  let good := {data | ∀ r n, 3 ≤ n → n < K →
    data ∈ onlineTrueW1StackPrefixGood (onlineMDPSuccessorRowLaw E)
      (onlineW3SquaredTrueFamily H E) K ((H : ℝ)^2) δ r n}
  let target : Set (OnlineResetTranscript State Action H K) :=
    {record | onlineObservedW3SquareCertificates H K E δ record.2}
  let observe := fun sample : (Fin K → State) × (OnlineMDPRow State Action H × Fin K → State) =>
    (sample.1, onlineStackHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
      (onlineFiniteStackExtend K fallback sample.2) (K * H))
  let encode := fun sample : (Fin K → State) × OnlineOutcomePath State (K * H) =>
    (sample.1, onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2)
  have hstack := onlineTrueW1Stack_allPrefixes_strict (onlineMDPSuccessorRowLaw E)
    (onlineW3SquaredTrueFamily H E) K hK ((H : ℝ)^2) δ (by positivity : 0 < (H : ℝ)^2)
    hδ hδsmall (onlineW3SquaredTrueFamily_range H E)
  have hlift : μ.real (Set.univ ×ˢ good) = (onlineMDPStackLaw E K).real good := by
    dsimp [μ, onlineMDPInitialStackLaw]
    rw [measureReal_def, Measure.prod_prod, measure_univ, one_mul]
    rfl
  have hsub : (Set.univ ×ˢ good) ⊆ observe ⁻¹' target := by
    intro sample hgood
    exact onlineW3SquareStackGood_implies_observed H K hH E sample.1 fallback planner δ sample.2 hgood.2
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  have hcouple : μ.map observe = ν.rowMeasure.map encode :=
    onlineStack_sequential_transcriptLaw_eq H K hH E ρ fallback planner (K * H) le_rfl
  have hprob : μ.real (observe ⁻¹' target) = ν.rowMeasure.real (encode ⁻¹' target) := by
    have h := congrArg (fun law : Measure (OnlineResetTranscript State Action H K) =>
      law.real target) hcouple
    simpa only [measureReal_def, Measure.map_apply (measurable_of_countable _)
      ((Set.to_countable target).measurableSet)] using h
  change 1 - 4 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ <
    ν.rowMeasure.real (encode ⁻¹' target)
  rw [← hprob]
  apply lt_of_lt_of_le _ (hlift.symm.le.trans hmono)
  simpa [good, onlineMDPStackLaw] using hstack
end StatisticalRL.OnlineRL
