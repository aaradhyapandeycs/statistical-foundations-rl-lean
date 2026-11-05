import Formalization.Online.Regret.MVP.Decoupling.OnlineMVPFutureProfileFamily
import Formalization.Online.Regret.MVP.Decoupling.MVPNormalizedSquare
import Formalization.Online.Regret.MVP.Probability.MVPStrongCorrectedUniform
import Formalization.Online.Regret.MVP.Probability.MVPSourceProfileIndex
import Formalization.Online.Regret.MVP.Probability.MVPCorrectedAllocation
import Formalization.Generative.FiniteHorizonGenerativeSampling

/-! Instantiate the corrected quarter-strong source-uniform estimate at the
actual fixed-profile future family and its normalized-square image. This is an
event-composition helper; the later dyadic/rank sums are separate. -/
namespace StatisticalRL.OnlineRL

open MeasureTheory ProbabilityTheory
open StatisticalRL.FiniteHorizonGenerative
open StatisticalRL.OnlineRL.MVPProfile
open scoped BigOperators

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance mvpQuarterFamilyStateMeasurable : MeasurableSpace State := ⊤

/-- The fixed finite family for one profile, stage and future code. Parameters
including the bonus scale are fixed before the product sample is drawn. -/
noncomputable def mvpActualValueSourceFamily
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (L c₁ c₂ : ℝ) :
    mvpUniformSourceProfile (State := State) (Action := Action) H K →
      (h : Fin H) → FutureCode (State := State) (Action := Action) h K →
        Finset (State → ℝ) :=
  fun p h code => onlineMVPSourceProfileFutureFamily hH (H : ℝ) L c₁ c₂ E p h code

/-- Image family for the normalized square `V²/H`; the source uniform lemma
will control the second-moment estimation terms with the same profile cover. -/
noncomputable def mvpActualNormalizedSquareSourceFamily
    {H K : ℕ} (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (L c₁ c₂ : ℝ) :
    mvpUniformSourceProfile (State := State) (Action := Action) H K →
      (h : Fin H) → FutureCode (State := State) (Action := Action) h K →
        Finset (State → ℝ) :=
  fun p h code =>
    mvp_normalizedSquareFamily (H : ℝ)
      (mvpActualValueSourceFamily hH E L c₁ c₂ p h code)

/-- The exact quarter-strong event from the source provider, made a named
predicate so the original and normalized-square applications can be
intersected without changing their quantifiers. -/
def mvpQuarterStrongSourceUniformEvent
    {H K : ℕ} (hK : 2 ≤ K) (E : Fin H → EnvironmentStage State Action) (δ : ℝ)
    (family : mvpUniformSourceProfile (State := State) (Action := Action) H K →
      (h : Fin H) → FutureCode (State := State) (Action := Action) h K →
        Finset (State → ℝ)) : Set (Samples State Action H K) :=
  {data | ∀ p : mvpUniformSourceProfile (State := State) (Action := Action) H K,
    ∀ l : mvpUniformLevel K,
    ∀ X : Fin H → State → Action → State → ℝ,
      (∀ h s a, X h s a ∈ family p h (futureData h K data)) →
      (∑ h : Fin H, ∑ s : State, ∑ a : Action,
        max ((FiniteDistribution.empiricalRow (mvpUniformBatchSize l)
            (mvpUniformBatchSize_pos l)
            (fun j => data ((h,s,a),
              mvpBatchIndex K (mvpUniformBatchSize l)
                (mvpUniformBatchSize_fits hK l) j))).expectation (X h s a) -
              ((E h).transition s a).expectation (X h s a)) 0) ≤
      let δp := onlineSourceOptimismDeltaPrime δ
        (Fintype.card State) (Fintype.card Action) H K
      let d := H * Fintype.card State * Fintype.card Action
      let x := Real.log K / Real.log 2
      let I := 40000 * x^3 * Real.log (3*d) * Real.log (1/δp)
      Real.sqrt ((d : ℝ) * I *
        (∑ h : Fin H, ∑ s : State, ∑ a : Action,
          ((E h).transition s a).variance (X h s a)) /
          (16 * (mvpUniformBatchSize l) * x)) +
        (d : ℝ) * (H : ℝ) * I /
          (16 * (mvpUniformBatchSize l) * x)}

/-- The two quarter-strong profile-family events hold together with the source
confidence. Their family, radius and failure allocation contain no random
profile, code, or table certificate as a premise. -/
theorem mvp_actualProfileFamilies_quarterStrong_intersection
    {H K : ℕ} (E : Fin H → EnvironmentStage State Action)
    (hH : 0 < H) (hK : 2 ≤ K)
    (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hc₁ : 4 ≤ c₁) (hc₂ : c₁^2 ≤ c₂)
    (hbudget : (K : ℝ) ≥
      (Fintype.card (Fin H × (State × Action)) : ℝ) * logTwoReal K) :
    let δp := onlineSourceOptimismDeltaPrime δ
      (Fintype.card State) (Fintype.card Action) H K
    let valueFamily := mvpActualValueSourceFamily (K := K) hH E
      (Real.log (1/δp)) c₁ c₂
    let squareFamily := mvpActualNormalizedSquareSourceFamily (K := K) hH E
      (Real.log (1/δp)) c₁ c₂
    1 - δp/2 ≤ (samplingLaw E K).real
      (mvpQuarterStrongSourceUniformEvent hK E δ valueFamily ∩
        mvpQuarterStrongSourceUniformEvent hK E δ squareFamily) ∧
      1 - δp/2 > 1 - δp := by
  classical
  letI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  let δp := onlineSourceOptimismDeltaPrime δ
    (Fintype.card State) (Fintype.card Action) H K
  let valueFamily := mvpActualValueSourceFamily (K := K) hH E (Real.log (1/δp)) c₁ c₂
  let squareFamily := mvpActualNormalizedSquareSourceFamily (K := K) hH E
    (Real.log (1/δp)) c₁ c₂
  let μ := samplingLaw E K
  have hS : 0 < Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
  have hA : 0 < Fintype.card Action := Fintype.card_pos_iff.mpr inferInstance
  have hδp := mvp_correctedAllocation_domain_and_log δ
    (Fintype.card State) (Fintype.card Action) H K hδ hδ1 hS hA hH (by omega)
  have hHreal : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hL : 0 ≤ Real.log (1/δp) := by linarith [hδp.2.2]
  have hc₁nonneg : 0 ≤ c₁ := by linarith
  have hc₂nonneg : 0 ≤ c₂ := by nlinarith [hc₂]
  have hVzero : ∀ p h code, (0 : State → ℝ) ∈ valueFamily p h code := by
    intro p h code
    exact onlineMVPSourceProfileFutureFamily_zero_mem hH (H : ℝ)
      (Real.log (1/δp)) c₁ c₂ E p h code
  have hVcard : ∀ p h code, (valueFamily p h code).card ≤ K + 1 := by
    intro p h code
    exact onlineMVPSourceProfileFutureFamily_card_le hH (H : ℝ)
      (Real.log (1/δp)) c₁ c₂ E p h code
  have hVbound : ∀ p h code V, V ∈ valueFamily p h code →
      ∀ x, 0 ≤ V x ∧ V x ≤ (H : ℝ) := by
    intro p h code V hV x
    exact onlineMVPSourceProfileFutureFamily_range hH E (H : ℝ)
      (Real.log (1/δp)) c₁ c₂ (by positivity) hL hc₁nonneg hc₂nonneg
      p h code hV x
  have hSzero : ∀ p h code, (0 : State → ℝ) ∈ squareFamily p h code := by
    intro p h code
    exact mvp_normalizedSquareFamily_zero (H : ℝ)
      (valueFamily p h code) (hVzero p h code)
  have hScard : ∀ p h code, (squareFamily p h code).card ≤ K + 1 := by
    intro p h code
    exact (mvp_normalizedSquareFamily_card (H : ℝ)
      (valueFamily p h code)).trans (hVcard p h code)
  have hSbound : ∀ p h code W, W ∈ squareFamily p h code →
      ∀ x, 0 ≤ W x ∧ W x ≤ (H : ℝ) := by
    intro p h code W hW
    exact mvp_normalizedSquareFamily_bounds (H : ℝ) hHreal
      (valueFamily p h code) (hVbound p h code) W hW
  have hvalue := StatisticalRL.FiniteHorizonGenerative.mvp_corrected_sourceUniform_quarterStrong_K2
    E hH K hK valueFamily hVzero hVcard hVbound δ hδ hδ1 hbudget
  have hsquare := StatisticalRL.FiniteHorizonGenerative.mvp_corrected_sourceUniform_quarterStrong_K2
    E hH K hK squareFamily hSzero hScard hSbound δ hδ hδ1 hbudget
  have hgoodValue : 1 - δp/4 ≤ μ.real
      (mvpQuarterStrongSourceUniformEvent hK E δ valueFamily) := by
    simpa [δp, μ, mvpQuarterStrongSourceUniformEvent] using hvalue
  have hgoodSquare : 1 - δp/4 ≤ μ.real
      (mvpQuarterStrongSourceUniformEvent hK E δ squareFamily) := by
    simpa [δp, μ, mvpQuarterStrongSourceUniformEvent] using hsquare
  have hbadValue : μ.real (mvpQuarterStrongSourceUniformEvent hK E δ valueFamily)ᶜ ≤ δp/4 := by
    have hc := measureReal_compl (μ := μ)
      ((Set.to_countable (mvpQuarterStrongSourceUniformEvent hK E δ valueFamily)).measurableSet)
    rw [probReal_univ] at hc
    linarith
  have hbadSquare : μ.real (mvpQuarterStrongSourceUniformEvent hK E δ squareFamily)ᶜ ≤ δp/4 := by
    have hc := measureReal_compl (μ := μ)
      ((Set.to_countable (mvpQuarterStrongSourceUniformEvent hK E δ squareFamily)).measurableSet)
    rw [probReal_univ] at hc
    linarith
  let bad := (mvpQuarterStrongSourceUniformEvent hK E δ valueFamily)ᶜ ∪
    (mvpQuarterStrongSourceUniformEvent hK E δ squareFamily)ᶜ
  have hbad : μ.real bad ≤ δp/2 := by
    calc
      μ.real bad ≤
          μ.real (mvpQuarterStrongSourceUniformEvent hK E δ valueFamily)ᶜ +
            μ.real (mvpQuarterStrongSourceUniformEvent hK E δ squareFamily)ᶜ :=
        measureReal_union_le _ _
      _ ≤ δp/4 + δp/4 := add_le_add hbadValue hbadSquare
      _ = δp/2 := by ring
  have hcompl := measureReal_compl (μ := μ)
    ((Set.to_countable bad).measurableSet)
  rw [probReal_univ] at hcompl
  have hgood : 1 - δp/2 ≤ μ.real badᶜ := by linarith
  have hset : badᶜ =
      mvpQuarterStrongSourceUniformEvent hK E δ valueFamily ∩
        mvpQuarterStrongSourceUniformEvent hK E δ squareFamily := by
    ext data
    simp [bad]
  have hstrict : 1 - δp/2 > 1 - δp := by linarith [hδp.1]
  have hgood' : 1 - δp/2 ≤ μ.real
      (mvpQuarterStrongSourceUniformEvent hK E δ valueFamily ∩
        mvpQuarterStrongSourceUniformEvent hK E δ squareFamily) := by
    rw [hset] at hgood
    exact hgood
  exact ⟨by simpa [δp, valueFamily, squareFamily, μ,
    mvpActualValueSourceFamily, mvpActualNormalizedSquareSourceFamily] using hgood', hstrict⟩

end StatisticalRL.OnlineRL
