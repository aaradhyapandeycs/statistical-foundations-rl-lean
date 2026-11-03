import Formalization.Online.SourceOptimism.StackPrefixBonusUnion
import Formalization.Online.SourceOptimism.ObservedEmpiricalPrefix
import Formalization.Online.SourceOptimism.CompletedEpisodeCount
import Formalization.Online.SourceOptimism.StackSequentialLawEquality

/-! Counterfactual all-prefix stack goodness
implies an observed-history certificate event; no measurability of the raw
counterfactual event with respect to observed history is asserted. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance onlineObservedEventStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance : DecidableEq State := Classical.decEq State
noncomputable local instance : DecidableEq Action := Classical.decEq Action

/-- The actual estimator-row certificate is a function only of the observed
pre-episode history. Counts0,1,2 remain the separate deterministic branch. -/
def onlineObservedPrefixBonusCertificates
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action)
    (V : OnlineMDPRow State Action H → State → ℝ) (δ c₁ c₂ : ℝ)
    (history : List (OnlineMDPRow State Action H × State)) : Prop :=
  ∀ k : Fin K, ∀ r : OnlineMDPRow State Action H,
    ∀ hn : 3≤(onlineRowOutcomes (history.take (k.val*H)) r).length,
    ∀ U : State → ℝ, (∀ s,V r s≤U s ∧ U s≤(H : ℝ)) →
      (onlineMDPSuccessorRowLaw E r).expectation (V r)≤
        (FiniteDistribution.empiricalRow _ (by omega)
          (onlineObservedRowData (history.take (k.val*H)) r)).expectation U+
        c₁*Real.sqrt ((FiniteDistribution.empiricalRow _ (by omega)
          (onlineObservedRowData (history.take (k.val*H)) r)).variance U*
          (Real.log (1/δ)/(onlineRowOutcomes (history.take (k.val*H)) r).length))+
        c₂*(H : ℝ)*(Real.log (1/δ)/
          (onlineRowOutcomes (history.take (k.val*H)) r).length)

/-- Every actual adaptive stack history has causally consistent row labels. -/
theorem onlineActualStackHistory_rows_consistent
    {Row Outcome : Type*} [DecidableEq Row]
    (choose : List (Row × Outcome) → Row) (stream : Row → ℕ → Outcome) (n : ℕ) :
    onlineTranscriptRowsConsistent choose (onlineStackHistory choose stream n) := by
  have hlen := onlineStackHistory_length choose stream n
  have heq : onlineStackHistory choose stream (onlineStackHistory choose stream n).length =
      onlineStackHistory choose stream n := by rw [hlen]
  exact ((onlineTranscriptSteps_iff_rows_and_coordinates choose stream _).mp
    ((onlineStackHistory_eq_iff_transcriptSteps choose stream _).mp heq)).1

/-- Every stage row's count before source episode k is below K on the actual
same stack history, not merely on a fixed or nonadaptive visitation table. -/
theorem onlineActualStack_preEpisode_count_le
    (H K : ℕ) (hH : 0<H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (k : Fin K)
    (r : OnlineMDPRow State Action H) :
    (onlineRowOutcomes (onlineStackHistory
      (onlineEpisodicChoose H K hH initial fallback planner)
      (onlineFiniteStackExtend K fallback data) (k.val*H)) r).length≤k.val := by
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let stream := onlineFiniteStackExtend K fallback data
  let history := onlineStackHistory choose stream (k.val*H)
  let rowAt := onlineTranscriptRowSequence (choose []) history
  have hlen : history.length=k.val*H := onlineStackHistory_length choose stream _
  have hr := onlineActualStackHistory_rows_consistent choose stream (k.val*H)
  have hrows (j : Fin history.length) : rowAt j.val=(history.get j).1 :=
    onlineTranscriptRowSequence_agrees _ _ _
  have hstage (j : ℕ) (hj : j<k.val*H) : (rowAt j).1.val=j%H := by
    have hj' : j<history.length := by simpa [hlen] using hj
    exact onlineEpisodicTranscript_stage H K hH initial fallback planner history hr
      rowAt hrows ⟨j,hj'⟩
  have hc := onlineVisitCount_completedEpisodes_le rowAt k.val hH r hstage
  have heq := onlineTranscript_rowCount_eq_visitCount history rowAt hrows
    history.length le_rfl r
  simp only [List.take_length] at heq
  rw [hlen] at heq
  exact heq.trans_le hc

/-- Key valid inclusion: simultaneous counterfactual stack-prefix certificates
imply certificates at all actually observed empirical rows before each episode.
The latter event is history-measurable; the former need not be. -/
theorem onlineStack_allPrefixGood_implies_observedCertificates
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (V : OnlineMDPRow State Action H → State → ℝ) (δ c₁ c₂ : ℝ)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (hgood : ∀ r n,3≤n → n<K →
      data∈onlineStackPrefixBonusGood (onlineMDPSuccessorRowLaw E) V K
        (H : ℝ) δ c₁ c₂ r n) :
    onlineObservedPrefixBonusCertificates H K E V δ c₁ c₂
      (onlineStackHistory (onlineEpisodicChoose H K hH initial fallback planner)
        (onlineFiniteStackExtend K fallback data) (K*H)) := by
  intro k r hn U hU
  let choose := onlineEpisodicChoose H K hH initial fallback planner
  let stream := onlineFiniteStackExtend K fallback data
  have hk : k.val*H≤K*H := Nat.mul_le_mul_right H k.isLt.le
  have htake := onlineStackHistory_take choose stream (K*H) (k.val*H) hk
  have hbound (hist : List (OnlineMDPRow State Action H × State))
      (heq : hist = onlineStackHistory choose stream (k.val*H))
      (hn' : 3 ≤ (onlineRowOutcomes hist r).length) :
      (onlineMDPSuccessorRowLaw E r).expectation (V r) ≤
        (FiniteDistribution.empiricalRow _ (by omega) (onlineObservedRowData hist r)).expectation U +
        c₁ * Real.sqrt ((FiniteDistribution.empiricalRow _ (by omega)
          (onlineObservedRowData hist r)).variance U *
          (Real.log (1/δ) / (onlineRowOutcomes hist r).length)) +
        c₂ * (H : ℝ) * (Real.log (1/δ) / (onlineRowOutcomes hist r).length) := by
    subst hist
    let history := onlineStackHistory choose stream (k.val*H)
    let N := (onlineRowOutcomes history r).length
    have hcount : N≤k.val := onlineActualStack_preEpisode_count_le H K hH initial
      fallback planner data k r
    have hnK : N<K := hcount.trans_lt k.isLt
    have hn3 : 3≤N := hn'
    have hcert := hgood r N hn3 hnK
    have hrow := onlineFiniteStack_empiricalRow_eq_prefix choose K (k.val*H) fallback
      data r hnK.le (by change 0 < N; omega)
    have hN : 3 ≤ N ∧ N < K := ⟨hn3, hnK⟩
    simp only [onlineStackPrefixBonusGood,dif_pos hN,Set.mem_setOf_eq] at hcert
    have h := hcert U hU
    rw [hrow]
    exact h
  exact hbound _ htake hn

end StatisticalRL.OnlineRL
