import Formalization.Online.SourceOptimism.ObservedPrefixProbability
import Formalization.Online.SourceOptimism.GreedySequentialBellmanOptimism

/-! OnlineW1TrueVariancePrefix: an intermediate component for the corrected-zero-count, fixed-tie W₁ analysis. Source-facing K≥2 scope and remaining W₂/regret obligations are stated at the final export. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance w1StateMeasurable : MeasurableSpace State := ⊤
local instance w1TranscriptMeasurable (H K : ℕ) :
    MeasurableSpace (OnlineResetTranscript State Action H K) := ⊤
local instance w1AtomMeasurable (K n : ℕ) :
    MeasurableSpace ((Fin K → State) × OnlineOutcomePath State n) := ⊤
noncomputable local instance OnlineW1TrueVariancePrefixLocalInstance1 : DecidableEq State := Classical.decEq State
noncomputable local instance OnlineW1TrueVariancePrefixLocalInstance2 : DecidableEq Action := Classical.decEq Action

/-- True-variance Bernstein radius for L = log(1/(2δ)). -/
noncomputable def onlineTrueW1Radius (H δ : ℝ) (n : ℕ)
    (d : FiniteDistribution State) (V : State → ℝ) : ℝ :=
  Real.sqrt (2 * Real.log (1 / (2 * δ)) * d.variance V / n) +
    2 * H * Real.log (1 / (2 * δ)) / (3 * n)

/-- Good event for a deterministic row/count prefix. Counts below three and
out-of-range counts are left unconstrained. -/
noncomputable def onlineTrueW1StackPrefixGood
    {Row : Type*} [Fintype Row] (d : Row → FiniteDistribution State)
    (V : Row → State → ℝ) (K : ℕ) (H δ : ℝ) (r : Row) (n : ℕ) :
    Set (Row × Fin K → State) :=
  if hn : 3 ≤ n ∧ n < K then
    {data | |(FiniteDistribution.empiricalRow n (by omega)
        (onlineStackRowPrefix K n (by omega) r data)).expectation (V r) - (d r).expectation (V r)| ≤
      onlineTrueW1Radius H δ n (d r) (V r)}
  else Set.univ

/-- Simultaneous fixed-prefix two-sided concentration under the actual stack
product law, with no random-count conditioning. -/
theorem onlineTrueW1Stack_allPrefixes_strict
    {Row : Type*} [Fintype Row] [Nonempty Row]
    (d : Row → FiniteDistribution State) (V : Row → State → ℝ)
    (K : ℕ) (hK : 0 < K) (H δ : ℝ) (hH : 0 < H)
    (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5)
    (hV : ∀ r s, V r s ∈ Set.Icc 0 H) :
    1 - 4 * (Fintype.card Row : ℝ) * K * δ <
      (onlineStackProductLaw (fun i : Row × Fin K => d i.1)).real
        {data | ∀ r n, 3 ≤ n → n < K → data ∈ onlineTrueW1StackPrefixGood d V K H δ r n} := by
  classical
  have hunion := onlineFixedPrefix_union_strict
    (onlineStackProductLaw (fun i : Row × Fin K => d i.1)) K hK (2 * δ)
    (by positivity) (onlineTrueW1StackPrefixGood d V K H δ)
  have hfixed : ∀ r n, 3 ≤ n → n < K →
      (onlineStackProductLaw (fun i : Row × Fin K => d i.1)).real
        (onlineTrueW1StackPrefixGood d V K H δ r n)ᶜ ≤ 2 * (2 * δ) := by
    intro r n hn hnK
    let good : Set (Fin n → State) := {data |
      |(FiniteDistribution.empiricalRow n (by omega) data).expectation (V r) - (d r).expectation (V r)| ≤
        onlineTrueW1Radius H δ n (d r) (V r)}
    have hL : 0 < Real.log (1 / (2 * δ)) := by
      apply Real.log_pos
      apply (lt_div_iff₀ (by positivity : 0 < 2 * δ)).2
      linarith
    have hbad := (d r).empiricalRow_source_threshold_strict (V r) n (by omega) H
      (Real.log (1 / (2 * δ))) hH.le hL (hV r)
    have hfailure : 2 * Real.exp (-Real.log (1 / (2 * δ))) = 4 * δ := by
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 1 / (2 * δ))]
      field_simp
      norm_num
    have hgood : 1 - 4 * δ ≤ ((d r).sampleMeasure n).real good := by
      have hc := measureReal_compl (μ := (d r).sampleMeasure n) ((Set.to_countable good).measurableSet)
      rw [probReal_univ] at hc
      have hb : ((d r).sampleMeasure n).real goodᶜ ≤ 4 * δ := by
        have hset : goodᶜ = {data : Fin n → State |
            onlineTrueW1Radius H δ n (d r) (V r) <
            |(FiniteDistribution.empiricalRow n (by omega) data).expectation (V r) - (d r).expectation (V r)|} := by
          ext data
          simp only [good, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
        rw [hset]
        simpa only [onlineTrueW1Radius, hfailure] using hbad
      linarith
    have heq : (onlineStackProductLaw (fun i : Row × Fin K => d i.1)).real
        ((onlineStackRowPrefix K n (by omega) r) ⁻¹' good) = ((d r).sampleMeasure n).real good := by
      rw [measureReal_def, ← Measure.map_apply (measurable_of_countable _)
        ((Set.to_countable good).measurableSet), onlineStackRowPrefix_map_law]
      rfl
    have hg : 1 - 4 * δ ≤ (onlineStackProductLaw (fun i : Row × Fin K => d i.1)).real
        (onlineTrueW1StackPrefixGood d V K H δ r n) := by
      rw [← heq] at hgood
      have hbounds : 3 ≤ n ∧ n < K := ⟨hn, hnK⟩
      simpa only [onlineTrueW1StackPrefixGood, dif_pos hbounds, good, Set.preimage_setOf_eq] using hgood
    have hc := measureReal_compl (μ := onlineStackProductLaw (fun i : Row × Fin K => d i.1))
      ((Set.to_countable (onlineTrueW1StackPrefixGood d V K H δ r n)).measurableSet)
    rw [probReal_univ] at hc
    linarith

  have hu := hunion hfixed
  nlinarith

/-- A bounded fixed value has a deterministic error bound for any two rows,
including empirical defaults at counts 0, 1 and 2. -/
theorem onlineTrueW1_bounded_error (p q : FiniteDistribution State) (V : State → ℝ)
    (H : ℝ) (hV : ∀ s, V s ∈ Set.Icc 0 H) :
    |q.expectation V - p.expectation V| ≤ H := by
  have hp0 := p.expectation_nonneg (fun s => (hV s).1)
  have hq0 := q.expectation_nonneg (fun s => (hV s).1)
  have hpH := p.expectation_le_const (fun s => (hV s).2)
  have hqH := q.expectation_le_const (fun s => (hV s).2)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Two-sided bounds at every actual completed-history row with count at
least three, for the same fixed true optimal continuation family. -/
noncomputable def onlineObservedTrueW1Certificates
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action) (δ : ℝ)
    (history : List (OnlineMDPRow State Action H × State)) : Prop :=
  ∀ k : Fin K, ∀ r : OnlineMDPRow State Action H,
    ∀ hn : 3 ≤ (onlineRowOutcomes (history.take (k.val * H)) r).length,
      let n := (onlineRowOutcomes (history.take (k.val * H)) r).length
      let emp := FiniteDistribution.empiricalRow n (by omega)
        (onlineObservedRowData (history.take (k.val * H)) r)
      let V := onlineTrueSuffixRowFamily E r
      |emp.expectation V - (onlineMDPSuccessorRowLaw E r).expectation V| ≤
        onlineTrueW1Radius (H : ℝ) δ n (onlineMDPSuccessorRowLaw E r) V

/-- Simultaneous deterministic-prefix goodness implies the same bound at
actual observed row counts. -/
theorem onlineTrueW1StackGood_implies_observed
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (δ : ℝ)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (hgood : ∀ r n, 3 ≤ n → n < K →
      data ∈ onlineTrueW1StackPrefixGood (onlineMDPSuccessorRowLaw E)
        (onlineTrueSuffixRowFamily E) K (H : ℝ) δ r n) :
    onlineObservedTrueW1Certificates H K E δ
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
      let V := onlineTrueSuffixRowFamily E r
      |emp.expectation V - (onlineMDPSuccessorRowLaw E r).expectation V| ≤
        onlineTrueW1Radius (H : ℝ) δ n (onlineMDPSuccessorRowLaw E r) V := by
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
positive-count W₁ row certificates hold simultaneously with the strict
factor-two finite-prefix confidence. -/
theorem onlineSequential_observedTrueW1Certificates_strict
    (H K : ℕ) (hH : 0 < H) (hK : 0 < K)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5) :
    1 - 4 * (Fintype.card (OnlineMDPRow State Action H) : ℝ) * K * δ <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        {sample | onlineObservedTrueW1Certificates H K E δ
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
      (onlineTrueSuffixRowFamily E) K (H : ℝ) δ r n}
  let target : Set (OnlineResetTranscript State Action H K) :=
    {record | onlineObservedTrueW1Certificates H K E δ record.2}
  let observe := fun sample : (Fin K → State) × (OnlineMDPRow State Action H × Fin K → State) =>
    (sample.1, onlineStackHistory (onlineEpisodicChoose H K hH sample.1 fallback planner)
      (onlineFiniteStackExtend K fallback sample.2) (K * H))
  let encode := fun sample : (Fin K → State) × OnlineOutcomePath State (K * H) =>
    (sample.1, onlineSequentialPathHistory
      (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2)
  have hstack := onlineTrueW1Stack_allPrefixes_strict (onlineMDPSuccessorRowLaw E)
    (onlineTrueSuffixRowFamily E) K hK (H : ℝ) δ (by exact_mod_cast hH)
    hδ hδsmall (onlineTrueSuffixRowFamily_range H E)
  have hlift : μ.real (Set.univ ×ˢ good) = (onlineMDPStackLaw E K).real good := by
    dsimp [μ, onlineMDPInitialStackLaw]
    rw [measureReal_def, Measure.prod_prod, measure_univ, one_mul]
    rfl
  have hsub : (Set.univ ×ˢ good) ⊆ observe ⁻¹' target := by
    intro sample hgood
    exact onlineTrueW1StackGood_implies_observed H K hH E sample.1 fallback planner δ sample.2 hgood.2
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
