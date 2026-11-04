import Formalization.ModelFree.TDConditionalMomentDefinitions
import Formalization.ModelFree.TDSourceFixedTerminalProxyDefinitions
import Formalization.ModelFree.QLearningSamplingDefinitions
import Formalization.ModelFree.QLearningComparisonDefinitions
import Formalization.ModelFree.QLearningRobustDefinitions

/-! Source-facing statement index for Chapter 4. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.Statements.Ch4
open StatisticalRL.TemporalDifference StatisticalRL.QLearning
universe u v
local instance stateMeasurable (State : Type*) : MeasurableSpace State := ⊤
local instance actionMeasurable (Action : Type*) : MeasurableSpace Action := ⊤

/-- `lemma:TD-bounded`, chapters/generative_model_model_free.tex:293–302. -/
def Lemma4_2 : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (samples : ℕ → State → State) (V₀ : State → ℝ)
    (T : ℕ), (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon) →
    (∀ k, k ≤ T → 0 ≤ η k ∧ η k ≤ 1) →
    ∀ t, t ≤ T →
    (∀ s, 0 ≤ tdIterate M π η samples V₀ t s ∧
      tdIterate M π η samples V₀ t s ≤ M.effectiveHorizon) ∧
    ‖tdIterate M π η samples V₀ t - M.trajectoryExpectedValue π‖ ≤ M.effectiveHorizon

/-- `lemma:TD-square`, chapters/generative_model_model_free.tex:643–659. -/
def Lemma4_4 : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ),
    (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon) →
    (∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1) →
    ∀ k, 1 ≤ k → k ≤ T →
    ∀ᵐ data ∂tdSamplingLaw M π T, ∀ s,
      η k * (1 - η k) * M.discount ^ 2 *
        (M.policyTransition π s).variance (tdValueBefore M π η T (k - 1) V₀ data) ≤
      (1 - η k) * tdValueBefore M π η T (k - 1) V₀ data s ^ 2 +
      η k * M.discount * (M.policyTransition π s).expectation
        (fun x ↦ tdValueBefore M π η T (k - 1) V₀ data x ^ 2) -
      (tdSamplingLaw M π T)[(fun d ↦ tdValueBefore M π η T k V₀ d s ^ 2) |
        tdPastSigma T (k - 1)] data + 2 * η k / (1 - M.discount)

/-- `lemma:TD-variance-proxy-bound`, chapters/generative_model_model_free.tex:727–743,
under the surrounding eligible-terminal condition at lines 488–490. The
book uses “small enough universal constants c₁ ≥ c₂ > 0”; the existing
proof supplies c₁ = c₂ = 1/4 and c₃ = 4096. -/
def Lemma4_5 : Prop :=
  ∃ c₁ c₂ c₃ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ 0 < c₃ ∧
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (δ ε : ℝ) (T t : ℕ),
    1/2 ≤ M.discount → 2 ≤ T → 0 < δ → δ < 1 → 0 < ε →
    ε ≤ M.effectiveHorizon → (∀ i, 1 ≤ i → i ≤ T →
      1 / (1 + c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 2) ≤ η i ∧
      η i ≤ 1 / (1 + c₂ * (1 - M.discount) * i / Real.log (T : ℝ) ^ 2)) →
    ∀ (V₀ : State → ℝ), (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon) →
    c₃ * Real.log (T : ℝ)^3 * Real.log ((Fintype.card State : ℝ)*T/δ) /
      ((1-M.discount)^3*ε^2) ≤ T →
    t ≤ T → (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ (t : ℝ) →
    1-δ/(2*T) ≤ (tdSamplingLaw M π T).real {data |
      ‖tdSourceFixedTerminalProxyVector M π η T t V₀
        (tdSourceBarEta M.discount T) data‖ ≤ 16*tdSourceBarEta M.discount T*M.effectiveHorizon^2 ∧
      ‖fun s => tdTerminalVarianceSum M π η T t V₀ s data‖ ≤
        33*Real.log (T : ℝ)^3/((1-M.discount)^3*T)}

/-- `lemma:non-negativity-Qt-Vt`, chapters/generative_model_model_free.tex:1052–1071. -/
def Lemma4_8 : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → Action → State) (Q₀ : State → Action → ℝ) (t : ℕ),
    (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
    (∀ k, 0 ≤ η k ∧ η k ≤ 1) →
    (∀ s a, 0 ≤ qLearningIterate M η samples Q₀ t s a ∧
      qLearningIterate M η samples Q₀ t s a ≤ M.effectiveHorizon) ∧
    (∀ s, 0 ≤ qLearningValue M (qLearningIterate M η samples Q₀ t) s ∧
      qLearningValue M (qLearningIterate M η samples Q₀ t) s ≤ M.effectiveHorizon) ∧
    ‖qLearningIterate M η samples Q₀ t - M.trajectoryExpectedQ M.optimalGreedyPolicy‖ ≤
      M.effectiveHorizon

/-- `lemma:Q-comparison-facts`, chapters/generative_model_model_free.tex:1338–1373. -/
def Lemma4_10 : Prop :=
  (∀ (State : Type u) [Fintype State] [Nonempty State]
    (p : FiniteDistribution State) (γ ρ : ℝ), 0 ≤ γ → γ < 1 → 0 < ρ →
    ∀ (v : State → ℝ), qChiValueSpan v ≤ 1 / (1 - γ) →
    (Real.sqrt (ρ * p.variance v) - ρ / (1 - γ) ≤
      sSup (qRobustExpectations p ρ v) - p.expectation v ∧
     sSup (qRobustExpectations p ρ v) - p.expectation v ≤ Real.sqrt (ρ * p.variance v)) ∧
    (Real.sqrt (ρ * p.variance v) - ρ / (1 - γ) ≤
      p.expectation v - sInf (qRobustExpectations p ρ v) ∧
     p.expectation v - sInf (qRobustExpectations p ρ v) ≤ Real.sqrt (ρ * p.variance v))) ∧
  (∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M M' : DiscountedMDP State Action) (ρ : ℝ), 0 < ρ →
    M'.reward = M.reward → M'.discount = M.discount →
    (∀ s a, M'.transition s a ∈ qChiBall (M.transition s a) ρ) →
    ‖M'.trajectoryExpectedQ M'.optimalGreedyPolicy -
      M.trajectoryExpectedQ M.optimalGreedyPolicy‖ ≤
      Real.sqrt (ρ * M.discount / (2 * (1 - M.discount) ^ 3)))

/-- `lemma:robust-Bellman-contraction`, chapters/generative_model_model_free.tex:1422–1438.
The reward shift is the source's b = 2ρ/(1−γ). -/
def Lemma4_11 : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (ρ : ℝ), 0 < ρ →
    let b := 2 * ρ / (1 - M.discount)
    ∀ Q R : State → Action → ℝ,
    ‖qRobustBellmanPlus M ρ b Q - qRobustBellmanPlus M ρ b R‖ ≤ M.discount * ‖Q - R‖ ∧
    ‖qRobustBellmanMinus M ρ b Q - qRobustBellmanMinus M ρ b R‖ ≤ M.discount * ‖Q - R‖

/-- `thm:infinite-horizon-simple`, chapters/generative_model_model_free.tex:891–912.
The book uses “small enough universal constants c₁ ≥ c₂ > 0”; the
existing proof supplies c₁ = c₂ = 1/4 and a sufficiently large c₃. -/
def Thm4_6 : Prop :=
  ∃ c₁ c₂ c₃ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ 0 < c₃ ∧
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ),
    1/2 ≤ M.discount → 2 ≤ Fintype.card Action → 2 ≤ T →
    0 < δ → δ < 1 → 0 < ε → ε ≤ M.effectiveHorizon →
    (∀ k, k ≤ T →
      1 / (1 + c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 3) ≤ η k ∧
      η k ≤ 1 / (1 + c₂ * (1 - M.discount) * k / Real.log (T : ℝ) ^ 3)) →
    ∀ (Q₀ : State → Action → ℝ),
    (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
    c₃ * Real.log (T : ℝ)^4 * Real.log
      ((Fintype.card State : ℝ)*(Fintype.card Action : ℝ)*T/δ) /
      ((1-M.discount)^4*ε^2) ≤ T →
    1-δ ≤ (qSamplingLaw M T).real {data | ∀ s a,
      |qSampledIterate M η T Q₀ data s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ ε}
end StatisticalRL.Statements.Ch4
