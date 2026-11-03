import Formalization.ModelFree.QLearningConditionalFinalAssembly

/-! Universal-constant wrapper for the CONDITIONAL accuracy
assembly. Comparator closeness remains explicit; this is not the source main
theorem or a proof of its missing stability prerequisite. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
universe u v

/-- A single constant chosen only from the fixed universal c2 satisfies every
sample-budget regularity condition used by the proved scalar conversion. -/
theorem qFinal_exists_universal_budget_constant (c₂ : ℝ) (hc₂ : 0 < c₂) :
    ∃ c₃ : ℝ, 0 < c₃ ∧ Real.exp 4 ≤ c₃*Real.log 2^5 ∧
      1 ≤ c₃*Real.log 2^2 ∧ 384 ≤ c₂*c₃*Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C := max (Real.exp 4 / Real.log 2^5)
    (max (1 / Real.log 2^2) (384 / (c₂*Real.log 2)))
  have h1 : Real.exp 4 / Real.log 2^5 ≤ C := le_max_left _ _
  have h2 : 1 / Real.log 2^2 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : 384 / (c₂*Real.log 2) ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hC : 0 < C := (div_pos (Real.exp_pos _) (pow_pos hlog _)).trans_le h1
  have he := (div_le_iff₀ (pow_pos hlog 5)).mp h1
  have hs := (div_le_iff₀ (pow_pos hlog 2)).mp h2
  have hd := (div_le_iff₀ (mul_pos hc₂ hlog)).mp h3
  exact ⟨C, hC, he, hs, by nlinarith [hd]⟩

/-- Fixed constants precede every carrier, model, confidence, accuracy, sample
budget and initialization. Closeness is an explicit separate input, so this
is a conditional source wrapper and cannot certify the unconditional theorem. -/
theorem qLearning_exists_universal_constants_conditional :
    ∃ c₁ c₂ c₃ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ c₁ ≤ 1 ∧ 0 < c₃ ∧
    ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ),
      1/2 ≤ M.discount → 2 ≤ Fintype.card Action → 2 ≤ T →
      0 < δ → δ < 1 → 0 < ε → ε ≤ M.effectiveHorizon →
      qSourceRateSchedule M.discount c₁ c₂ T η →
      ∀ (Q₀ : State → Action → ℝ),
      (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
      c₃*Real.log (T:ℝ)^4*Real.log
        ((Fintype.card State:ℝ)*(Fintype.card Action:ℝ)*T/δ)/((1-M.discount)^4*ε^2) ≤ T →
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
  obtain ⟨C, hC, he, hs, hd⟩ := qFinal_exists_universal_budget_constant (1/4) (by norm_num)
  refine ⟨1/4, 1/4, C, by norm_num, by norm_num, by norm_num, hC, ?_⟩
  intro State Action instState instAction M η δ ε T hγhalf _hA hT hδ hδ1 hε hεmax hschedule Q₀ h₀ hbudget
  exact qLearning_conditional_source_accuracy M η (1/4) (1/4) C δ ε T hγhalf (by norm_num)
    (by norm_num) (by norm_num) hC he hs hd hT hδ hδ1 hε hεmax hschedule Q₀ h₀ hbudget

end StatisticalRL.QLearning
