import Formalization.Online.Regret.MVP.Optimism.MVPBatchBonus
import Formalization.Online.SourceOptimism.GreedySequentialBellmanOptimism
import Formalization.Online.SourceOptimism.SourceOptimismAllocation

/-! Corrected source allocation and fixed true continuation for MVP batches. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance mvpTrueSuffixBonusStateMeasurable : MeasurableSpace State := ⊤

/-- One actual expanded product experiment supplies every nontrivial fixed
MVP batch certificate for the true optimal continuation. -/
theorem mvp_trueSuffix_allBatchBonus_probability {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (hH : 0<H) (K : ℕ) (hK : 0<K)
    (δ c₁ c₂ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) (hc₁ : 4≤c₁) (hc₂ : c₁^2≤c₂) :
    let δp := onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K
    1-2*(Fintype.card State : ℝ)*Fintype.card Action*H*K*δp <
      (samplingLaw E K).real {data | ∀ r n, 3≤n → n<K →
        data ∈ mvpBatchBonusGood E (onlineTrueSuffixRowFamily E) K δp c₁ c₂ r n} := by
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := (E ⟨0,hH⟩).action_nonempty
  have hs : 0 < Fintype.card State := Fintype.card_pos_iff.mpr inferInstance
  have ha : 0 < Fintype.card Action := Fintype.card_pos_iff.mpr inferInstance
  have hd := onlineSourceOptimismDeltaPrime_domain δ (Fintype.card State)
    (Fintype.card Action) H K hδ hδ1 hs ha hH hK
  have hsmall : onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K ≤ 2/5 := by
    linarith [hd.2]
  have h := mvp_allBatchBonusGood_probability E hH K hK (onlineTrueSuffixRowFamily E)
    (onlineSourceOptimismDeltaPrime δ (Fintype.card State) (Fintype.card Action) H K)
    c₁ c₂ hd.1 hsmall hc₁ hc₂ (onlineTrueSuffixRowFamily_range H E)
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, mul_assoc,
    mul_left_comm, mul_comm] using h
end StatisticalRL.FiniteHorizonGenerative
