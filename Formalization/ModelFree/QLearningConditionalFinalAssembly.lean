import Formalization.ModelFree.QLearningComparatorSameData
import Formalization.ModelFree.QLearningFinalBudgetConsequences

/-! Conditional assembly. The only missing statistical/model
input is explicitly the separately stated comparator-closeness hypothesis;
this file does not assert the unconditional source main theorem. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qConditionalFinalStateMeasurable : MeasurableSpace State := ⊤
local instance qConditionalFinalActionMeasurable : MeasurableSpace Action := ⊤

/-- Actual-law error radius from the actual same-data sandwich and separate
comparator closeness. Proof-argument quantification changes no comparator. -/
theorem qComparator_conditional_errorRadius_probability (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (c₁ c₂ δ : ℝ) (T : ℕ) (hT : 2 ≤ T)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hs : qSourceRateSchedule M.discount c₁ c₂ T η)
    (Q₀ : State → Action → ℝ) (h₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon)
    (D : ℝ) :
    let ρ := qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
      (Fintype.card State) (Fintype.card Action) T
    (∀ (hρ : 0 ≤ ρ) s a,
      |qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ D ∧
      |qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ D) →
    1 - δ ≤ (qSamplingLaw M T).real {data | ∀ s a,
      |qSampledIterate M η T Q₀ data s a - M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤
        ((1+2*ρ+Real.sqrt ρ)*M.effectiveHorizon)*qComparatorRadiusProduct M.discount η (T/2) T + D} := by
  dsimp only
  intro hclose
  obtain ⟨hρ, hp⟩ := qComparator_actualSandwich_probability M η c₁ c₂ δ T hT hc₁ hc₂ hδ hδ1 hs Q₀ h₀
  apply hp.trans
  apply measureReal_mono
  · intro data hd s a
    have hh := hd T (Nat.div_le_self _ _) le_rfl s a
    exact qFinal_sandwich_error hh (hclose hρ s a).2 (hclose hρ s a).1
  · exact measure_ne_top _ _

/-- Conditional source-shaped final accuracy assembly: the main sample budget
and actual algorithm are consumed, but source part(ii) comparator closeness is
an explicit separate hypothesis and is not proved or hidden by this theorem. -/
theorem qLearning_conditional_source_accuracy (M : DiscountedMDP State Action)
    (η : ℕ → ℝ) (c₁ c₂ c₃ δ ε : ℝ) (T : ℕ)
    (hγhalf : 1/2 ≤ M.discount) (hc₁ : 0 < c₁) (hc₁1 : c₁ ≤ 1)
    (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hexp : Real.exp 4 ≤ c₃*Real.log 2^5) (hconst : 1 ≤ c₃*Real.log 2^2)
    (hden : 384 ≤ c₂*c₃*Real.log 2)
    (hT : 2 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hεmax : ε ≤ M.effectiveHorizon)
    (hs : qSourceRateSchedule M.discount c₁ c₂ T η)
    (Q₀ : State → Action → ℝ) (h₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon)
    (hbudget : c₃*Real.log (T:ℝ)^4*Real.log
      ((Fintype.card State:ℝ)*(Fintype.card Action:ℝ)*T/δ)/((1-M.discount)^4*ε^2) ≤ T) :
    let ρ := qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
      (Fintype.card State) (Fintype.card Action) T
    let D := Real.sqrt (M.discount*ρ/(2*(1-M.discount)^3)) + 2*ρ/(1-M.discount)^2
    (∀ (hρ : 0 ≤ ρ) s a,
      |qRobustPlusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ D ∧
      |qRobustMinusFixedPoint M ρ (2*ρ*M.effectiveHorizon) hρ s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ D) →
    1 - δ ≤ (qSamplingLaw M T).real {data | ∀ s a,
      |qSampledIterate M η T Q₀ data s a - M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ ε} := by
  dsimp only
  intro hclose
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  let ρ := qChiSourceRadius (qChiSourceRateEnvelope M.discount c₂ T) δ
    (Fintype.card State) (Fintype.card Action) T
  let D := Real.sqrt (M.discount*ρ/(2*(1-M.discount)^3)) + 2*ρ/(1-M.discount)^2
  have hp := qComparator_conditional_errorRadius_probability M η c₁ c₂ δ T hT hc₁ hc₂ hδ hδ1 hs Q₀ h₀ D hclose
  have hb := qFinal_source_scalar_radius_le M.discount c₁ c₂ c₃ δ ε
    (Fintype.card State) (Fintype.card Action) T η hγhalf M.discount_lt_one hc₁ hc₁1 hc₂ hc₃
    hexp hconst hden (Fintype.card_pos_iff.mpr M.state_nonempty)
    (Fintype.card_pos_iff.mpr M.action_nonempty) hT hδ hδ1 hε hεmax hs hbudget
  have hbound : ((1+2*ρ+Real.sqrt ρ)*M.effectiveHorizon)*qComparatorRadiusProduct M.discount η (T/2) T + D ≤ ε := by
    simpa only [DiscountedMDP.effectiveHorizon, qComparatorRadiusProduct, div_eq_mul_inv, one_mul,
      add_assoc] using hb
  apply hp.trans
  apply measureReal_mono
  · intro data hd s a
    exact (hd s a).trans hbound
  · exact measure_ne_top _ _

end StatisticalRL.QLearning
