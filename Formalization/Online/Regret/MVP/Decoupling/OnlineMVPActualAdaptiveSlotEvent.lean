import Formalization.Online.Regret.MVP.Decoupling.MVPSourceProfileQuarterEvents
import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPFutureProfileBatchCongruence
import Formalization.Online.Regret.MVP.Decoupling.MVPVisitValueLookup
import Formalization.Online.Regret.MVP.Decoupling.MVPNormalizedSquare

/-! Consume the profile-uniform event at the actual data-adaptive values of
finite dyadic visit slots. The profile and future code are selected from the
observed sample only after the event's universal quantifiers are available. -/
namespace StatisticalRL.OnlineRL

open MeasureTheory ProbabilityTheory
open StatisticalRL.FiniteHorizonGenerative
open StatisticalRL.OnlineRL.MVPProfile
open StatisticalRL.OnlineRL.MVPUniformSource
open scoped BigOperators

variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance mvpAdaptiveSlotStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance mvpAdaptiveSlotStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpAdaptiveSlotActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The one source profile formed from all pre-episode rows of the actual
stack transcript. It is chosen as a parameter to the uniform event, not frozen
before the data. -/
noncomputable def mvpActualAdaptiveSourceProfile
    {H K : ℕ} (hH : 0 < H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) :
    mvpUniformSourceProfile (State := State) (Action := Action) H K :=
  sourceMVPActualProfileTable
    (fun e h => (onlineMVPActualStackRowAt hH initial fallback planner data
      (e * H + h.val)).2)

/-- The value table frozen at each episode's pre-episode planning history. -/
noncomputable def mvpActualAdaptiveValueTable
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (L c₁ c₂ : ℝ) (h : Fin H) : Fin K → State → ℝ :=
  fun k => onlineCappedBackwardValueAt (H : ℝ) L c₁ c₂
    (onlineMVPActualPreEpisodeStages hH E initial fallback planner data k) (h.val + 1)

/-- The stage-h row sequence observed over the actual episode transcript. -/
noncomputable def mvpActualAdaptiveStageRows
    {H K : ℕ} (hH : 0 < H) (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State) (h : Fin H) :
    ℕ → State × Action :=
  fun k => (onlineMVPActualStackRowAt hH initial fallback planner data
    (k * H + h.val)).2

/-- The value-function test vector for one adaptive visit rank. -/
noncomputable def mvpActualAdaptiveValueSlotTest
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (L c₁ c₂ : ℝ) (j : Fin (Nat.log2 K)) (i : Fin (2 * 2 ^ j.val)) :
    Fin H → State → Action → State → ℝ :=
  fun h s a => mvp_visitValueLookup
    (mvpActualAdaptiveStageRows hH initial fallback planner data h) K (s, a)
    (2 * 2 ^ j.val + i.val)
    (mvpActualAdaptiveValueTable hH E initial fallback planner data L c₁ c₂ h)

/-- The normalized-square test vector uses the same adaptive visit lookup. -/
noncomputable def mvpActualAdaptiveSquareSlotTest
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (L c₁ c₂ : ℝ) (j : Fin (Nat.log2 K)) (i : Fin (2 * 2 ^ j.val)) :
    Fin H → State → Action → State → ℝ :=
  fun h s a => mvp_normalizedSquare (H : ℝ)
    (mvpActualAdaptiveValueSlotTest hH E initial fallback planner data
      L c₁ c₂ j i h s a)

/-- Every actual value-slot vector belongs to the one fixed-profile family
whose profile and future code are selected from the current sample. -/
theorem mvpActualAdaptiveValueSlotTest_mem
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (L c₁ c₂ : ℝ) (j : Fin (Nat.log2 K)) (i : Fin (2 * 2 ^ j.val)) :
    ∀ h s a, mvpActualAdaptiveValueSlotTest hH E initial fallback planner data
        L c₁ c₂ j i h s a ∈
      mvpActualValueSourceFamily hH E L c₁ c₂
        (mvpActualAdaptiveSourceProfile hH initial fallback planner data) h
        (MVPUniformSource.futureData h K data) := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  intro h s a
  let p := mvpActualAdaptiveSourceProfile hH initial fallback planner data
  let family := onlineMVPSourceProfileFutureFamily hH (H : ℝ) L c₁ c₂ E p h
    (MVPUniformSource.futureData h K data)
  have hzero : (0 : State → ℝ) ∈ family := by
    exact onlineMVPSourceProfileFutureFamily_zero_mem hH (H : ℝ) L c₁ c₂ E p h
      (MVPUniformSource.futureData h K data)
  have hvalues : ∀ k : Fin K,
      mvpActualAdaptiveValueTable hH E initial fallback planner data L c₁ c₂ h k ∈ family := by
    intro k
    simpa [mvpActualAdaptiveValueTable, p, mvpActualAdaptiveSourceProfile] using
      onlineMVPActualPreEpisodeValue_mem_sourceProfileFamily_noFallback
        hH hK E initial fallback planner data (H : ℝ) L c₁ c₂ k h
  simpa [mvpActualValueSourceFamily, mvpActualAdaptiveValueSlotTest,
    mvpActualAdaptiveStageRows, mvpActualAdaptiveValueTable, family] using
    mvp_visitValueLookup_mem
      (mvpActualAdaptiveStageRows hH initial fallback planner data h) K (s, a)
      (2 * 2 ^ j.val + i.val)
      (mvpActualAdaptiveValueTable hH E initial fallback planner data L c₁ c₂ h)
      family hzero hvalues

/-- The normalized-square adaptive vector belongs to the image family used by
second-moment uniform control. -/
theorem mvpActualAdaptiveSquareSlotTest_mem
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (initial : Fin K → State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (L c₁ c₂ : ℝ) (j : Fin (Nat.log2 K)) (i : Fin (2 * 2 ^ j.val)) :
    ∀ h s a, mvpActualAdaptiveSquareSlotTest hH E initial fallback planner data
        L c₁ c₂ j i h s a ∈
      mvpActualNormalizedSquareSourceFamily hH E L c₁ c₂
        (mvpActualAdaptiveSourceProfile hH initial fallback planner data) h
        (MVPUniformSource.futureData h K data) := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  intro h s a
  let p := mvpActualAdaptiveSourceProfile hH initial fallback planner data
  let family := onlineMVPSourceProfileFutureFamily hH (H : ℝ) L c₁ c₂ E p h
    (MVPUniformSource.futureData h K data)
  let squareFamily := mvp_normalizedSquareFamily (H : ℝ) family
  have hzero : (0 : State → ℝ) ∈ squareFamily := by
    exact mvp_normalizedSquareFamily_zero (H : ℝ) family
      (onlineMVPSourceProfileFutureFamily_zero_mem hH (H : ℝ) L c₁ c₂ E p h
        (MVPUniformSource.futureData h K data))
  have hvalues : ∀ k : Fin K,
      mvp_normalizedSquare (H : ℝ)
        (mvpActualAdaptiveValueTable hH E initial fallback planner data L c₁ c₂ h k) ∈
        squareFamily := by
    intro k
    apply mvp_normalizedSquareFamily_mem (H : ℝ) family _
    simpa [mvpActualAdaptiveValueTable, p, mvpActualAdaptiveSourceProfile] using
      onlineMVPActualPreEpisodeValue_mem_sourceProfileFamily_noFallback
        hH hK E initial fallback planner data (H : ℝ) L c₁ c₂ k h
  have hmap : mvp_normalizedSquare (H : ℝ)
      (mvp_visitValueLookup (mvpActualAdaptiveStageRows hH initial fallback planner data h)
        K (s, a) (2 * 2 ^ j.val + i.val)
        (mvpActualAdaptiveValueTable hH E initial fallback planner data L c₁ c₂ h)) =
      mvp_visitValueLookup (mvpActualAdaptiveStageRows hH initial fallback planner data h)
        K (s, a) (2 * 2 ^ j.val + i.val)
        (fun k => mvp_normalizedSquare (H : ℝ)
          (mvpActualAdaptiveValueTable hH E initial fallback planner data L c₁ c₂ h k)) := by
    simpa [mvp_normalizedSquare] using
      (mvp_visitValueLookup_map
        (mvpActualAdaptiveStageRows hH initial fallback planner data h) K (s, a)
        (2 * 2 ^ j.val + i.val)
        (mvpActualAdaptiveValueTable hH E initial fallback planner data L c₁ c₂ h)
        (mvp_normalizedSquare (H : ℝ))
        (mvp_normalizedSquare_zero (H : ℝ)))
  change mvp_normalizedSquare (H : ℝ)
      (mvp_visitValueLookup (mvpActualAdaptiveStageRows hH initial fallback planner data h)
        K (s, a) (2 * 2 ^ j.val + i.val)
        (mvpActualAdaptiveValueTable hH E initial fallback planner data L c₁ c₂ h)) ∈
    mvp_normalizedSquareFamily (H : ℝ) family
  rw [hmap]
  simpa [mvpActualNormalizedSquareSourceFamily, mvpActualValueSourceFamily,
    mvpActualAdaptiveSquareSlotTest, mvpActualAdaptiveStageRows,
    mvpActualAdaptiveValueTable, p, mvpActualAdaptiveSourceProfile,
    family, squareFamily] using
    mvp_visitValueLookup_mem
      (mvpActualAdaptiveStageRows hH initial fallback planner data h) K (s, a)
      (2 * 2 ^ j.val + i.val)
      (fun k => mvp_normalizedSquare (H : ℝ)
        (mvpActualAdaptiveValueTable hH E initial fallback planner data L c₁ c₂ h k))
      squareFamily hzero hvalues

/-- Apply the value-family uniform event at each actual adaptive rank slot. -/
theorem mvpActualAdaptiveValueSlot_bound_of_quarterEvent
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (δ L c₁ c₂ : ℝ)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (hgood : data ∈ mvpQuarterStrongSourceUniformEvent hK E δ
      (mvpActualValueSourceFamily hH E L c₁ c₂))
    (ell : mvpUniformLevel K)
    (j : Fin (Nat.log2 K)) (i : Fin (2 * 2 ^ j.val)) :
    (∑ h : Fin H, ∑ s : State, ∑ a : Action,
      max ((FiniteDistribution.empiricalRow (mvpUniformBatchSize ell)
          (mvpUniformBatchSize_pos ell)
          (fun q => data ((h, s, a), mvpBatchIndex K
            (mvpUniformBatchSize ell) (mvpUniformBatchSize_fits hK ell) q))).expectation
          (mvpActualAdaptiveValueSlotTest hH E initial fallback planner data
            L c₁ c₂ j i h s a) -
        ((E h).transition s a).expectation
          (mvpActualAdaptiveValueSlotTest hH E initial fallback planner data
            L c₁ c₂ j i h s a)) 0) ≤
      let δp := onlineSourceOptimismDeltaPrime δ
        (Fintype.card State) (Fintype.card Action) H K
      let d := H * Fintype.card State * Fintype.card Action
      let x := Real.log K / Real.log 2
      let I := 40000 * x^3 * Real.log (3*d) * Real.log (1/δp)
      Real.sqrt ((d : ℝ) * I *
        (∑ h : Fin H, ∑ s : State, ∑ a : Action,
          ((E h).transition s a).variance
            (mvpActualAdaptiveValueSlotTest hH E initial fallback planner data
              L c₁ c₂ j i h s a)) /
          (16 * (mvpUniformBatchSize ell) * x)) +
      (d : ℝ) * (H : ℝ) * I / (16 * (mvpUniformBatchSize ell) * x) := by
  classical
  let p := mvpActualAdaptiveSourceProfile hH initial fallback planner data
  let test := mvpActualAdaptiveValueSlotTest hH E initial fallback planner data
    L c₁ c₂ j i
  have hmem : ∀ h s a, test h s a ∈
      mvpActualValueSourceFamily hH E L c₁ c₂ p h (MVPUniformSource.futureData h K data) := by
    simpa [test, p, mvpActualAdaptiveSourceProfile] using
      mvpActualAdaptiveValueSlotTest_mem hH hK E initial fallback planner data L c₁ c₂ j i
  exact hgood p ell test hmem

/-- Apply the normalized-square family event at each actual adaptive rank
slot; the image-family membership is obtained by applying `V ↦ V²/H` to the
same lookup. -/
theorem mvpActualAdaptiveSquareSlot_bound_of_quarterEvent
    {H K : ℕ} (hH : 0 < H) (hK : 2 ≤ K)
    (E : Fin H → EnvironmentStage State Action) (δ L c₁ c₂ : ℝ)
    (initial : Fin K → State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H)
    (data : OnlineMDPRow State Action H × Fin K → State)
    (hgood : data ∈ mvpQuarterStrongSourceUniformEvent hK E δ
      (mvpActualNormalizedSquareSourceFamily hH E L c₁ c₂))
    (ell : mvpUniformLevel K)
    (j : Fin (Nat.log2 K)) (i : Fin (2 * 2 ^ j.val)) :
    (∑ h : Fin H, ∑ s : State, ∑ a : Action,
      max ((FiniteDistribution.empiricalRow (mvpUniformBatchSize ell)
          (mvpUniformBatchSize_pos ell)
          (fun q => data ((h, s, a), mvpBatchIndex K
            (mvpUniformBatchSize ell) (mvpUniformBatchSize_fits hK ell) q))).expectation
          (mvpActualAdaptiveSquareSlotTest hH E initial fallback planner data
            L c₁ c₂ j i h s a) -
        ((E h).transition s a).expectation
          (mvpActualAdaptiveSquareSlotTest hH E initial fallback planner data
            L c₁ c₂ j i h s a)) 0) ≤
      let δp := onlineSourceOptimismDeltaPrime δ
        (Fintype.card State) (Fintype.card Action) H K
      let d := H * Fintype.card State * Fintype.card Action
      let x := Real.log K / Real.log 2
      let I := 40000 * x^3 * Real.log (3*d) * Real.log (1/δp)
      Real.sqrt ((d : ℝ) * I *
        (∑ h : Fin H, ∑ s : State, ∑ a : Action,
          ((E h).transition s a).variance
            (mvpActualAdaptiveSquareSlotTest hH E initial fallback planner data
              L c₁ c₂ j i h s a)) /
          (16 * (mvpUniformBatchSize ell) * x)) +
      (d : ℝ) * (H : ℝ) * I / (16 * (mvpUniformBatchSize ell) * x) := by
  classical
  let p := mvpActualAdaptiveSourceProfile hH initial fallback planner data
  let test := mvpActualAdaptiveSquareSlotTest hH E initial fallback planner data
    L c₁ c₂ j i
  have hmem : ∀ h s a, test h s a ∈
      mvpActualNormalizedSquareSourceFamily hH E L c₁ c₂ p h
        (MVPUniformSource.futureData h K data) := by
    simpa [test, p, mvpActualAdaptiveSourceProfile] using
      mvpActualAdaptiveSquareSlotTest_mem hH hK E initial fallback planner data L c₁ c₂ j i
  exact hgood p ell test hmem

end StatisticalRL.OnlineRL
