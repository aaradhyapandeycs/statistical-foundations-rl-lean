import Formalization.Online.Regret.MVP.Probability.MVPStrongProfileSourceRadius
import Formalization.Online.Regret.MVP.Probability.MVPSourceProfileIndex
import Formalization.Online.Regret.MVP.Probability.MVPCorrectedAllocation

/-! strengthened corrected-allocation uniform event: quarter failure budget. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance mvpCorrectedQuarterStateMeasurable : MeasurableSpace State := ⊤

theorem mvp_corrected_sourceUniform_quarterStrong_K2 {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (hH : 0 < H) (K : ℕ) (hK : 2 ≤ K)
    (family : mvpUniformSourceProfile (State := State) (Action := Action) H K →
      (h : Fin H) → FutureCode (State := State) (Action := Action) h K → Finset (State → ℝ))
    (hzero : ∀ p h code, (0 : State → ℝ) ∈ family p h code)
    (hcard : ∀ p h code, (family p h code).card ≤ K+1)
    (hbound : ∀ p h code V, V ∈ family p h code → ∀ x, 0 ≤ V x ∧ V x ≤ H)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hbudget : (K : ℝ) ≥ (Fintype.card (Fin H × (State × Action)) : ℝ) *
      StatisticalRL.OnlineRL.MVPProfile.logTwoReal K) :
    let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    let d := H*Fintype.card State*Fintype.card Action
    let x := Real.log K/Real.log 2
    let I := 40000*x^3*Real.log (3*d)*Real.log (1/δp)
    1 - δp/4 ≤ (samplingLaw E K).real {data | ∀ p : mvpUniformSourceProfile (State := State) (Action := Action) H K, ∀ l : mvpUniformLevel K,
      ∀ X : Fin H → State → Action → State → ℝ,
      (∀ h s a, X h s a ∈ family p h (futureData h K data)) →
      (∑ h : Fin H, ∑ s : State, ∑ a : Action,
        max ((FiniteDistribution.empiricalRow (mvpUniformBatchSize l) (mvpUniformBatchSize_pos l)
            (fun j => data ((h,s,a),mvpBatchIndex K (mvpUniformBatchSize l) (mvpUniformBatchSize_fits hK l) j))).expectation (X h s a) -
              ((E h).transition s a).expectation (X h s a)) 0) ≤
      Real.sqrt ((d : ℝ)*I*(∑ h : Fin H, ∑ s : State, ∑ a : Action,
        ((E h).transition s a).variance (X h s a))/(16*(mvpUniformBatchSize l)*x)) +
        (d : ℝ)*(H : ℝ)*I/(16*(mvpUniformBatchSize l)*x)} := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  have hs : 0 < Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
  have ha : 0 < Fintype.card Action := Fintype.card_pos_iff.mpr inferInstance
  have hk : 0 < K := by omega
  let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
  have hd := mvp_correctedAllocation_domain_and_log δ (Fintype.card State) (Fintype.card Action) H K
    hδ hδ1 hs ha hH hk
  have hc := mvpUniformSourceProfile_card_bound (State := State) (Action := Action) H K
    hH hs ha hK hbudget
  have hc' : (Fintype.card (mvpUniformSourceProfile (State := State) (Action := Action) H K) : ℝ) ≤
      (4*(H*Fintype.card State*Fintype.card Action : ℕ)*K : ℝ) ^
        ((H*Fintype.card State*Fintype.card Action : ℕ) * (Real.log K/Real.log 2) + 1) := by
    simpa [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, StatisticalRL.OnlineRL.MVPProfile.logTwoReal,
      mul_assoc, mul_left_comm, mul_comm] using hc
  exact mvp_profileFamily_quarterSourceRadius E hH K hK family hzero hcard hbound δp hd.1 hd.2.1 hc'
end StatisticalRL.FiniteHorizonGenerative
