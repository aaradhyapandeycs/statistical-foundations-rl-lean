import Formalization.Online.Regret.MVP.Probability.MVPProfileUniform
import Formalization.Online.Regret.MVP.Probability.MVPDyadicLevel

/-! The explicit-log result specialized to all source dyadic batch levels. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action Profile : Type*} [Fintype State] [Fintype Action]
  [Fintype Profile] [Nonempty Profile]
local instance : MeasurableSpace State := ⊤
noncomputable local instance mvpDSDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance mvpDADecidable : DecidableEq Action := Classical.decEq Action
noncomputable local instance mvpDChoiceFintype (H K : ℕ) :
    Fintype (mvpProfileChoiceIndex (Profile := Profile) (Level := mvpUniformLevel K) (State := State) (Action := Action) H K) := by
  unfold mvpProfileChoiceIndex mvpUniformLevel
  infer_instance

theorem mvp_profileFamily_dyadicUniform {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (K : ℕ) (hK : 2 ≤ K)
    (family : Profile → (h : Fin H) → FutureCode (State := State) (Action := Action) h K → Finset (State → ℝ))
    (hzero : ∀ p h code, (0 : State → ℝ) ∈ family p h code)
    (hcard : ∀ p h code, (family p h code).card ≤ K+1)
    (hbound : ∀ p h code V, V ∈ family p h code → ∀ x, 0 ≤ V x ∧ V x ≤ H)
    (peels : ℕ) (hp : 0 < peels) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let Idx := mvpProfileChoiceIndex (Profile := Profile) (Level := mvpUniformLevel K) (State := State) (Action := Action) H K
    let Mask := Fin H → State → Action → Bool
    let ε := δ / (Fintype.card (Idx × Mask) : ℝ)
    1 - δ ≤ (samplingLaw E K).real {data | ∀ p : Profile, ∀ l : mvpUniformLevel K,
      ∀ X : Fin H → State → Action → State → ℝ,
      (∀ h s a, X h s a ∈ family p h (futureData h K data)) →
      (∑ h : Fin H, ∑ s : State, ∑ a : Action,
        max ((FiniteDistribution.empiricalRow (mvpUniformBatchSize l) (mvpUniformBatchSize_pos l)
            (fun j => data ((h,s,a),mvpBatchIndex K (mvpUniformBatchSize l) (mvpUniformBatchSize_fits hK l) j))).expectation (X h s a) -
              ((E h).transition s a).expectation (X h s a)) 0) ≤
      (Real.sqrt (8 * max
          (((mvpUniformBatchSize l : ℕ) : ℝ) * ∑ h : Fin H, ∑ s : State, ∑ a : Action,
            ((E h).transition s a).variance (X h s a))
          ((((mvpUniformBatchSize l : ℕ) : ℝ) * H * Fintype.card State * Fintype.card Action * (H : ℝ)^2) / (2 : ℝ)^peels) *
          Real.log (2 * peels / ε)) + (4/3) * H * Real.log (2 * peels / ε)) / mvpUniformBatchSize l} := by
  classical
  have hlog : 0 < Nat.log2 K := by
    have h : 1 ≤ Nat.log2 K := (Nat.le_log2 (by omega)).2 (by simpa using hK)
    omega
  letI : Fintype (mvpUniformLevel K) := by unfold mvpUniformLevel; infer_instance
  letI : Nonempty (mvpUniformLevel K) := ⟨⟨0,hlog⟩⟩
  exact mvp_profileFamily_uniformExplicit E K mvpUniformBatchSize
    (fun l => mvpUniformBatchSize_fits hK l) (fun l => mvpUniformBatchSize_pos l)
    family hzero hcard hbound peels hp δ hδ hδ1
end StatisticalRL.FiniteHorizonGenerative
