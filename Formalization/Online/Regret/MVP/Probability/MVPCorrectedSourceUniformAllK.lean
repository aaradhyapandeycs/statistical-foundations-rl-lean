import Formalization.Online.Regret.MVP.Probability.MVPProfileSourceRadius
import Formalization.Online.Regret.MVP.Probability.MVPSourceProfileIndex
import Formalization.Online.Regret.MVP.Probability.MVPCorrectedAllocation
import Formalization.Online.Regret.MVP.Probability.MVPLevelFromExistence
import Formalization.Online.Regret.MVP.Probability.MVPCorrectedSourceUniform

/-! Corrected-allocation MVP uniform concentration on the actual expanded law. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

theorem mvp_corrected_sourceUniform {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (hH : 0 < H) (K : ℕ) (hK : 1 ≤ K)
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
    1 - δp ≤ (samplingLaw E K).real {data | ∀ p : mvpUniformSourceProfile (State := State) (Action := Action) H K, ∀ l : mvpUniformLevel K,
      ∀ X : Fin H → State → Action → State → ℝ,
      (∀ h s a, X h s a ∈ family p h (futureData h K data)) →
      (∑ h : Fin H, ∑ s : State, ∑ a : Action,
        max ((FiniteDistribution.empiricalRow (mvpUniformBatchSize l) (mvpUniformBatchSize_pos l)
            (fun j => data ((h,s,a),mvpBatchIndex K (mvpUniformBatchSize l) (mvpUniformBatchSize_fits_of_level l) j))).expectation (X h s a) -
              ((E h).transition s a).expectation (X h s a)) 0) ≤
      Real.sqrt ((d : ℝ)*I*(∑ h : Fin H, ∑ s : State, ∑ a : Action,
        ((E h).transition s a).variance (X h s a))/(4*(mvpUniformBatchSize l)*x)) +
        (d : ℝ)*(H : ℝ)*I/(4*(mvpUniformBatchSize l)*x)} := by
  classical
  by_cases hK2 : 2 ≤ K
  · exact mvp_corrected_sourceUniform_K2 E hH K hK2 family hzero hcard hbound δ hδ hδ1 hbudget
  · have hK1 : K = 1 := by omega
    subst K
    have hset : {data : Samples State Action H 1 | ∀ p : mvpUniformSourceProfile (State := State) (Action := Action) H 1,
        ∀ l : mvpUniformLevel 1, True} = Set.univ := by
      ext data
      simp [mvpUniformLevel]
    have hevent : {data : Samples State Action H 1 | ∀ p : mvpUniformSourceProfile (State := State) (Action := Action) H 1,
        ∀ l : mvpUniformLevel 1, True} = Set.univ := hset
    have hδp : 0 ≤ onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H 1 := by
      letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
      letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
      exact (mvp_correctedAllocation_domain_and_log δ (Fintype.card State) (Fintype.card Action) H 1 hδ hδ1
        (Fintype.card_pos_iff.mpr inferInstance) (Fintype.card_pos_iff.mpr inferInstance) hH (by omega)).1.le
    letI : IsEmpty (mvpUniformLevel 1) := by
      change IsEmpty (Fin 0)
      infer_instance
    simp only [IsEmpty.forall_iff, implies_true, forall_const, Set.setOf_true, probReal_univ]
    linarith
end StatisticalRL.FiniteHorizonGenerative
