import Formalization.ModelFree.QLearningHardMDPDefinitions
import Formalization.ModelFree.QLearningLowerBoundDefinitions
import Formalization.ModelFree.TDConditionalMomentDefinitions
import Formalization.ModelFree.TDSourceFixedTerminalProxyDefinitions
import Formalization.ModelFree.TDSourceSamplingDefinitions
import Formalization.ModelFree.QLearningSamplingDefinitions
import Formalization.ModelFree.QLearningComparisonDefinitions
import Formalization.ModelFree.QLearningRobustDefinitions
import Formalization.ModelFree.FiniteQ.Definitions
import Formalization.ModelFree.AsyncQ.Definitions

/-! Source-facing statement index for Chapter 4. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.Statements.Ch4
open StatisticalRL.TemporalDifference StatisticalRL.QLearning
universe u v
local instance stateMeasurable (State : Type*) : MeasurableSpace State := ⊤
local instance actionMeasurable (Action : Type*) : MeasurableSpace Action := ⊤

/-- `thm:policy-evaluation-TD`, `chapters/generative_model_model_free.tex:179–224`.
The book uses "small enough universal constants c₁ ≥ c₂ > 0" and "sufficiently large c₃". They
are read as: there is a threshold `c₀ > 0` such that for EVERY `0 < c₂ ≤ c₁ ≤ c₀` (every schedule
in the family) there is a universal `c₃ > 0` (depending only on `c₁`, `c₂`), chosen before the
model, `δ`, `ε` and `T`. This is the same shape as `Thm4_13_corrected` and implies the weaker
reading `∃ c₁ ≥ c₂ ∃ c₃`. The proof takes `c₀ = 1/4` and
`c₃ = max(4096, e^{1/c₂}/(log 2)^4, 4/c₁, 1/(c₁ (log 2)²))`. The indexed event uses exactly the
source's T synchronous samples and compares the resulting iterate with the true
infinite-trajectory policy value. -/
def Thm4_1 : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ c₂ : ℝ, 0 < c₂ → c₂ ≤ c₁ → c₁ ≤ c₀ → ∃ c₃ : ℝ, 0 < c₃ ∧
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ),
    1 / 2 ≤ M.discount → M.discount < 1 → 2 ≤ T →
    0 < δ → δ < 1 → 0 < ε → ε ≤ 1 / (1 - M.discount) →
    (∀ t, 1 ≤ t → t ≤ T →
      1 / (1 + c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 2) ≤ η t ∧
      η t ≤ 1 / (1 + c₂ * (1 - M.discount) * t / Real.log (T : ℝ) ^ 2)) →
    ∀ (V₀ : State → ℝ),
    (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ 1 / (1 - M.discount)) →
    c₃ * Real.log (T : ℝ) ^ 3 *
      Real.log ((Fintype.card State : ℝ) * T / δ) /
        ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ) →
    1 - δ ≤ (tdSourceSamplingLaw M π T).real
      {data | ∀ s : State,
        |tdSourceSampledIterate M π η T V₀ data s -
          M.trajectoryExpectedValue π s| ≤ ε}

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
The book uses "small enough universal constants c₁ ≥ c₂ > 0" and "sufficiently large c₃". They
are read as: there is a threshold `c₀ > 0` such that for EVERY `0 < c₂ ≤ c₁ ≤ c₀` (every schedule
in the family, including the constant and rescaled-linear rates) there is a universal `c₃ > 0`
(depending only on `c₂`), chosen before the model, `δ`, `ε`, `T` and the initialization. This is
the same shape as `Thm4_13_corrected` and implies the weaker reading `∃ c₁ ≥ c₂ ∃ c₃`. The proof
takes `c₀ = 1`. -/
def Thm4_6 : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ c₂ : ℝ, 0 < c₂ → c₂ ≤ c₁ → c₁ ≤ c₀ → ∃ c₃ : ℝ, 0 < c₃ ∧
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

/-- Learning-rate discussion after Theorem 4.6 (`thm:infinite-horizon-simple`,
`chapters/generative_model_model_free.tex:891–912`), `chapters/generative_model_model_free.tex:945–953` (schedule `eq:thm:infinite-horizaon-eta`,
`chapters/generative_model_model_free.tex:882–886`; iteration condition `eq:thm:infinite-horizon-T`, :896–899): the schedule "permits"
the constant rate `η ≡ 1/(1 + c₁(1−γ)T/log³T)`, which is `Õ((1−γ)³ε²)` when `T` is at the
threshold. Stated for all constants `c₁ ≥ c₂ > 0` (in particular for the witnesses of `Thm4_6`):
(i) the constant rate satisfies both schedule bounds at every `0 ≤ k ≤ T`; (ii) when `T` meets
the iteration condition with constant `c₃ > 0`, the rate is at most
`(1−γ)³ε²/(c₁ c₃ log T · log(SAT/δ))`, which makes the `Õ` explicit (the hidden factor is
`1/(c₁c₃ log T log(SAT/δ))`). The printed "`T ≍` threshold" is used only in its `≥` direction,
which is what an upper bound on `η` needs. -/
def Thm4_6_constantRate : Prop :=
  ∀ (c₁ c₂ c₃ γ ε δ : ℝ) (S A T : ℕ), 0 < c₂ → c₂ ≤ c₁ → 0 < c₃ → 0 ≤ γ → γ < 1 → 0 < ε →
    0 < δ → δ < 1 → 1 ≤ S → 1 ≤ A → 2 ≤ T →
    let η : ℝ := 1 / (1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 3)
    (∀ k : ℕ, k ≤ T →
      1 / (1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 3) ≤ η ∧
      η ≤ 1 / (1 + c₂ * (1 - γ) * k / Real.log (T : ℝ) ^ 3)) ∧
    (c₃ * Real.log (T : ℝ) ^ 4 * Real.log ((S : ℝ) * A * T / δ) / ((1 - γ) ^ 4 * ε ^ 2) ≤ T →
      η ≤ (1 - γ) ^ 3 * ε ^ 2 / (c₁ * c₃ * Real.log (T : ℝ) * Real.log ((S : ℝ) * A * T / δ)))

/-- Under-estimation discussion after Theorem 4.6 (`thm:infinite-horizon-simple`),
paragraph "Discussion: over-estimation vs. under-estimation",
`chapters/generative_model_model_free.tex:1869–1881` (display `:1873–1879`; Q-learning
`alg:q-infinite` `:841–870`, schedule `eq:thm:infinite-horizaon-eta` `:881–886`,
Theorem 4.6 `:891–912`).

`Q̃` (`qPolicySampledIterate`) uses the same initialization and the same exact-T
transition samples as Q-learning (`qSampledIterate`), but takes the next action from a
deterministic optimal policy `f` (`V^f = V⋆` at every state) instead of maximizing.

* Clause 1 (`Q̃_T ≤ Q_T`, the first display inequality) holds pathwise, for every data
  array.
* Clause 2 makes the printed `−Õ(√(1/((1−γ)³T)))·1_{SA}` explicit: with probability at
  least `1−δ` under the actual synchronous sampling law, simultaneously for all `(s,a)`,
  `Q̃_T − Q⋆ ≥ −C·√(log⁴T · log(SAT/δ) / ((1−γ)³T))`. The hidden polylog is exactly
  `log⁴T · log(SAT/δ)` (C = 91 in the proof).
* There is no budget premise on `T` (only `T ≥ 2`) and no `A ≥ 2` premise; both are
  stronger than the printed context.
* RESTRICTED: proved only for the single schedule pair `c₁ = c₂ = 1`. The statement is existential
  (`∃ c₁ c₂ C`), unlike `Thm4_6`, which now covers every `0 < c₂ ≤ c₁ ≤ 1`; the reading "for every
  sufficiently small `c₁ ≥ c₂ > 0`" is not established. This is a limit of the proof
  infrastructure (the transported TD analysis needs `c₂ ≥ 1` after rewriting the `log³T` schedule
  as a `log²T` schedule with `T`-dependent constants), not a source error; see
  [`SOURCE-ISSUES.md#C52`](../../docs/SOURCE-ISSUES.md#C52). A prose claim, not a numbered result. -/
def Thm4_6_underestimation_restricted : Prop :=
  ∃ c₁ c₂ C : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ 0 < C ∧
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (η : ℕ → ℝ) (δ : ℝ) (T : ℕ),
    1 / 2 ≤ M.discount → 2 ≤ T → 0 < δ → δ < 1 →
    (∀ k, k ≤ T →
      1 / (1 + c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 3) ≤ η k ∧
      η k ≤ 1 / (1 + c₂ * (1 - M.discount) * k / Real.log (T : ℝ) ^ 3)) →
    ∀ (Q₀ : State → Action → ℝ), (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
    ∀ (f : State → Action),
      (∀ s, M.trajectoryExpectedValue (fun x ↦ EnvironmentStage.pointMass (f x)) s =
        M.trajectoryExpectedValue M.optimalGreedyPolicy s) →
    (∀ (data : QSamples State Action T) s a,
        qPolicySampledIterate M f η T Q₀ data s a ≤ qSampledIterate M η T Q₀ data s a) ∧
    1 - δ ≤ (qSamplingLaw M T).real {data | ∀ s a,
      -(C * Real.sqrt (Real.log (T : ℝ) ^ 4 *
          Real.log ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T / δ) /
          ((1 - M.discount) ^ 3 * T))) ≤
        qPolicySampledIterate M f η T Q₀ data s a -
          M.trajectoryExpectedQ M.optimalGreedyPolicy s a}
/-- Corrected Lemma 4.3, `lemma:TD-step-size`, `chapters/generative_model_model_free.tex:317–327`,
with the schedule `eq:thm:eta-TD` (`chapters/generative_model_model_free.tex:182–185`) and the weights `η_k^{(t)}` of
`def:eta-k-t` (`chapters/generative_model_model_free.tex:308–313`) written out (the `k = 0` branch takes precedence at `t = 0`).

Differences from the printed lemma (see `docs/SOURCE-ISSUES.md`, Candidate C5): the printed
statement omits the γ-dependent sample-size premise `log² T ≤ c₁ (1-γ) T` used by its appendix
proof, and does not bound `t` by the horizon `T` on which the schedule is constrained; both are
assumed here, together with `T ≥ 2` so that `log T > 0`. The standing
discount convention `γ ∈ [0,1)` is made explicit. The printed early-weight bound fails
without the extra premise (`Formalization/ModelFree/TDStandaloneStepSizeCounterexample.lean`).
The source's standing `c₁ ≥ c₂` is not needed. The case `0 ≤ k ≤ t/2` is written `2k ≤ t`. -/
def Lemma4_3_corrected : Prop :=
  ∀ (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ),
    2 ≤ T → 0 ≤ γ → γ < 1 → 0 < c₁ → 0 < c₂ → c₁ * c₂ ≤ 1 / 8 →
    Real.log (T : ℝ) ^ 2 ≤ c₁ * (1 - γ) * T →
    (∀ i : ℕ, 1 ≤ i → i ≤ T →
      1 / (1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 2) ≤ η i ∧
      η i ≤ 1 / (1 + c₂ * (1 - γ) * i / Real.log (T : ℝ) ^ 2)) →
    ∀ (t k : ℕ), t ≤ T → k ≤ t → (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ t →
      let w : ℝ := if k ≤ t then (if k = 0 then 1 else η k) *
          ∏ i ∈ Finset.Icc (k + 1) t, (1 - η i * (1 - γ)) else 0
      (2 * k ≤ t → w ≤ 1 / (T : ℝ) ^ 2) ∧
      (t < 2 * k → w ≤ η k ∧ η k ≤ 2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T))

/-- Lemma 4.9, `lemma:Q-step-size`, `chapters/generative_model_model_free.tex:1093–1112`, under
the learning-rate schedule `eq:thm:infinite-horizaon-eta` (`chapters/generative_model_model_free.tex:882–886`), with
`η̄ = min{1, 2 log³T / (c₂(1-γ)T)}` of `eq:Q-comparison-parameters` (`chapters/generative_model_model_free.tex:1087–1089`) and the
weights `η_i^{(t)}` of `def:eta-i-t-simple` (`chapters/generative_model_model_free.tex:1075–1083`) written out; the `i = 0` branch
takes precedence at `t = 0`. `T / 2` is natural-number division, i.e. `⌊T/2⌋`. The horizon is
assumed to satisfy `T ≥ 2`, so that `log T > 0` and the schedule is well defined. The source's
standing `c₁ ≥ c₂` is not needed; the square-sum bound is stated for every `t ≤ T` (it is an
empty sum when `t ≤ ⌊T/2⌋`). -/
def Lemma4_9 : Prop :=
  ∀ (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ),
    2 ≤ T → γ < 1 → 0 < c₁ → 0 < c₂ →
    (∀ k : ℕ, k ≤ T →
      1 / (1 + c₁ * (1 - γ) * (T : ℝ) / Real.log (T : ℝ) ^ 3) ≤ η k ∧
      η k ≤ 1 / (1 + c₂ * (1 - γ) * (k : ℝ) / Real.log (T : ℝ) ^ 3)) →
    let ηbar : ℝ := min 1 (2 * Real.log (T : ℝ) ^ 3 / (c₂ * (1 - γ) * (T : ℝ)))
    let w : ℕ → ℕ → ℝ := fun t i =>
      if i = 0 then ∏ j ∈ Finset.Icc 1 t, (1 - η j)
      else η i * ∏ j ∈ Finset.Icc (i + 1) t, (1 - η j)
    (∀ i t : ℕ, T / 2 < i → i ≤ t → t ≤ T → 0 ≤ w t i ∧ w t i ≤ η i ∧ η i ≤ ηbar) ∧
    (∀ t : ℕ, t ≤ T → (∑ i ∈ Finset.Icc (T / 2 + 1) t, (w t i) ^ 2) ≤ ηbar) ∧
    (∀ τ t : ℕ, 1 ≤ τ → τ ≤ t →
      (∑ i ∈ Finset.Icc τ t, w t i) = 1 - ∏ j ∈ Finset.Icc τ t, (1 - η j)) ∧
    (∀ t : ℕ, (∑ i ∈ Finset.Icc 0 t, w t i) = 1)

/-- Lemma 4.14, `lem:optimal-V-Q-hardMDP`, `chapters/generative_model_model_free.tex:2797–2811`,
for the hard MDP `M_hard` of lines 2735–2781 with `p = (4γ-1)/(3γ)` (`defn-parameter-p-Q-lower`, lines 2784–2788).
`qHardMDP γ` has states `Fin 4` and actions `Bool`: the source's state-dependent action sets
(`A₁ = {1,2}`, all others `{1}`) are encoded by giving every state two actions, which at states
0, 2 and 3 are copies of the single source action; claims about `Q⋆(s,1)` are stated for every
action. `V⋆` and `Q⋆` are the trajectory values of the optimal greedy policy. The statement is
proved for every `1/4 < γ < 1` (where `0 < p < 1`), which contains the source's lower-bound
regime `3/4 ≤ γ < 1`. The copied-action encoding is harmless for these optimal values but is
not suitable for the Q-learning dynamics (`docs/SOURCE-ISSUES.md#C31`, item 5): Theorem 4.7 and
Lemma 4.15 use the dominated-dummy-action instance `qLbMDP`, whose values (the same closed forms)
are `qLbMDP_optimal_values` in `Formalization/ModelFree/QLearningLowerBoundValues.lean`. -/
def Lemma4_14 : Prop :=
  ∀ (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1),
    let M := qHardMDP γ hγ hγ1
    let p : ℝ := (4 * γ - 1) / (3 * γ)
    let Vs := M.trajectoryExpectedValue M.optimalGreedyPolicy
    let Qs := M.trajectoryExpectedQ M.optimalGreedyPolicy
    (Vs 0 = 0 ∧ ∀ a, Qs 0 a = 0) ∧
    (Vs 1 = 1 / (1 - γ * p) ∧ (∀ a, Qs 1 a = 1 / (1 - γ * p)) ∧
      Vs 2 = 1 / (1 - γ * p) ∧ (∀ a, Qs 2 a = 1 / (1 - γ * p)) ∧
      1 / (1 - γ * p) = 3 / (4 * (1 - γ))) ∧
    (Vs 3 = 1 / (1 - γ) ∧ ∀ a, Qs 3 a = 1 / (1 - γ))


/-- Restricted Theorem 4.7, `thm:LB-example-Q-generative`,
`chapters/generative_model_model_free.tex:969–982`; proof Appendix C, lines 2707–3944.

Implied by `Thm4_7`; retained for history. It states only case (ii), constant learning rates
`η_t ≡ η ∈ (0,1)`. The full printed statement, including case (i) (rescaled linear rates
`η_t = 1/(1 + c_η(1-γ)t)`, which the source defers to li2024q, `docs/SOURCE-ISSUES.md#C30`), is the
entry `Thm4_7`.

Encoding: `max_s E[|V_T(s) - V⋆(s)|²] ≥ b` is written `∃ s, b ≤ E[…]` (finite state set). The
MDP has `S = 4` states (`Fin 4`) and `A = 2` actions (`Bool`) at every state, with rewards in
`[0,1]` and discount `γ` (fields of `DiscountedMDP`). `V_T` is the output of Algorithm
`alg:q-infinite` (`chapters/generative_model_model_free.tex:841–870`; synchronous generative Q-learning, `qSampledIterate`) after `T` rounds from
`Q₀ ≡ 0` under the genuine product sampling law `qSamplingLaw M T`. `V⋆` is the trajectory value of
the optimal greedy policy (the project convention). `log` is the natural logarithm.

The proof's witness is the source's `M_hard` with dominated dummy actions at states 0, 2, 3
(`qLbMDP γ`, depending only on `γ`), since the source's state-dependent action sets must be padded
to two actions without changing the Q-learning recursions (`docs/SOURCE-ISSUES.md#C31`, item 5).
The proof does not follow the printed Freedman route of Lemma 4.15 or the printed Step 5.4 closed
form, which contain constant slips and an off-by-one (`docs/SOURCE-ISSUES.md#C31`); the export uses
`c₃ = 16` and `c_lb = e^{-16}`. -/
def Thm4_7_restricted : Prop :=
  ∃ c₃ c_lb : ℝ, 0 < c₃ ∧ 0 < c_lb ∧
  ∀ γ : ℝ, 3 / 4 ≤ γ → γ < 1 → ∀ T : ℕ, c₃ / (1 - γ) ^ 2 ≤ T →
  ∀ η : ℝ, 0 < η → η < 1 →
  ∃ M : DiscountedMDP (Fin 4) Bool, M.discount = γ ∧ ∃ s : Fin 4,
    c_lb / ((1 - γ) ^ 4 * T * Real.log T ^ 2) ≤
      ∫ data, (qLearningValue M (qSampledIterate M (fun _ ↦ η) T (fun _ _ ↦ 0) data) s -
        M.trajectoryExpectedValue M.optimalGreedyPolicy s) ^ 2 ∂qSamplingLaw M T

/-- Lemma 4.15, `lem:lower-bound-E-xi-lower-Q`, `chapters/generative_model_model_free.tex:3429–3449`;
proof lines 3707–3944.

The implicit Step-5 context (lines 3270–3420) is written out: `3/4 ≤ γ < 1`, `T ≥ c₃/(1-γ)²`, and
the moderate constant rate `4/((1-γ)T) < η < 1/((1-γ)²T)`. The hard instance is `qLbMDP γ` (`M_hard`
with dominated dummy actions), `p = (4γ-1)/(3γ)`. `ξ_{t,max} = max_a ξ_t(a)` (`qLbXiMax`,
`eqn:defn-xi-t`, `chapters/generative_model_model_free.tex:3406–3412`) is built from the auxiliary sequence `Q̂_t` (`qLbAuxIterate`,
`eqn:Qhat-schumann`, `chapters/generative_model_model_free.tex:3316–3324`, initialized at `Q⋆(1,a) = 1/(1-γp)`) driven by the state-1
draws of the independent generative sample stream. `τ̂` is the largest natural number `τ` with
`(1-η(1-γp))^{T-τ+1} ≤ 6/7` (`eq:tau-hat-byproduct-duplicate`); its existence (the source's
remark) is part of the Prop. "For all `t ≥ τ̂`" is encoded by running the experiment to any horizon
`N ≥ t` (`qSamplingLaw (qLbMDP γ) N`, stream `qSamplesExtend`), so `t` is not bounded by `T`.
The printed proof has constant slips (`docs/SOURCE-ISSUES.md#C31`, item 3); only the unnamed
constant `c` is affected, and the export uses `c = 1/320`, `c₃ = 16`. -/
def Lemma4_15 : Prop :=
  ∃ c c₃ : ℝ, 0 < c ∧ 0 < c₃ ∧
  ∀ (γ : ℝ) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (T : ℕ) (η : ℝ),
    c₃ / (1 - γ) ^ 2 ≤ T → 4 / ((1 - γ) * T) < η → η < 1 / ((1 - γ) ^ 2 * T) →
    let p : ℝ := (4 * γ - 1) / (3 * γ)
    let ρ : ℝ := 1 - η * (1 - γ * p)
    (∃ τ : ℕ, ρ ^ (T + 1 - τ) ≤ 6 / 7 ∧ ∀ τ' : ℕ, ρ ^ (T + 1 - τ') ≤ 6 / 7 → τ' ≤ τ) ∧
    ∀ τhat : ℕ, ρ ^ (T + 1 - τhat) ≤ 6 / 7 →
      (∀ τ' : ℕ, ρ ^ (T + 1 - τ') ≤ 6 / 7 → τ' ≤ τhat) →
      ∀ t N : ℕ, τhat ≤ t → t ≤ N →
        c / (Real.sqrt ((1 - γ) ^ 2 * T) * Real.log T) ≤
          ∫ data, qLbXiMax γ η (qSamplesExtend (qLbMDP γ (by linarith) hγ1) N data) t
            ∂qSamplingLaw (qLbMDP γ (by linarith) hγ1) N

/-- Remark 4.5, `chapters/generative_model_model_free.tex:3455–3457`, in the setting of
Lemma 4.15 (`lem:lower-bound-E-xi-lower-Q`, :3429–3449): `ξ_t(a)` and `ξ_{t,max}` of
`eqn:defn-xi-t` (:3405–3411), built from the auxiliary sequence `Q̂`, `V̂` of `eqn:Qhat-schumann`
(:3316–3324) on the hard instance `qLbMDP γ` with constant rate `η` and `p = (4γ−1)/(3γ)`,
`P_k(1∣1,a) = qLbStay … 1 k a`, the sample stream of the experiment run to horizon `N ≥ t`.
The closing sentence ((1−γ)⁻³ vs (1−γ)⁻⁴) is explanatory and is not formalized.

(i) The mechanism of "single action ⇒ `E ξ = 0`": for *any* value process `W` whose value
`W n` depends only on the state-1 draws at times `1, …, n` (as `V̂` does, whatever the number of
actions), `E[∑_{k=1}^t η(1−η)^{t−k} γ (P_k(1∣1,a) − p) W_{k−1}] = 0`.
(ii) The single-action case itself: with only the action `a`, the auxiliary recursion is
`Q̂_0 = 1/(1−γp)`, `Q̂_{k+1} = (1−η)Q̂_k + η(1 + γ P_{k+1}(1∣1,a) Q̂_k)`, `V̂ = Q̂`, and
`ξ_{t,max} = ξ_t(a)`; its mean is `0`. The single-action experiment is represented by the
action-`a` draws at state 1 of the two-action experiment, which have the single-action law
(`P(1∣1,a) = p`, independent across times).
(iii) "`E ξ_{t,max}` is strictly positive" is read on Lemma 4.15's range `t ≥ τ̂` and regime
(`T ≥ c₃/(1−γ)²`, `4/((1−γ)T) < η < 1/((1−γ)²T)`); at `t = 0`, `ξ = 0`, so positivity for every
`t` is false. -/
def Remark4_5 : Prop :=
  (∀ (γ : ℝ) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (η : ℝ) (N t : ℕ) (a : Bool), t ≤ N →
    let p : ℝ := (4 * γ - 1) / (3 * γ)
    (∀ W : ℕ → (ℕ → Fin 4 → Bool → Fin 4) → ℝ,
      (∀ n samples samples', (∀ k, 1 ≤ k → k ≤ n → ∀ b, samples k 1 b = samples' k 1 b) →
        W n samples = W n samples') →
      ∫ data, ∑ k ∈ Finset.Icc 1 t, η * (1 - η) ^ (t - k) * γ *
          (qLbStay (qSamplesExtend (qLbMDP γ (by linarith) hγ1) N data) 1 k a - p) *
          W (k - 1) (qSamplesExtend (qLbMDP γ (by linarith) hγ1) N data)
        ∂qSamplingLaw (qLbMDP γ (by linarith) hγ1) N = 0) ∧
    (let Qhat : (ℕ → Fin 4 → Bool → Fin 4) → ℕ → ℝ := fun samples n ↦
        Nat.rec (1 / (1 - γ * p))
          (fun k q ↦ (1 - η) * q + η * (1 + γ * qLbStay samples 1 (k + 1) a * q)) n
      ∫ data, ∑ k ∈ Finset.Icc 1 t, η * (1 - η) ^ (t - k) * γ *
          (qLbStay (qSamplesExtend (qLbMDP γ (by linarith) hγ1) N data) 1 k a - p) *
          Qhat (qSamplesExtend (qLbMDP γ (by linarith) hγ1) N data) (k - 1)
        ∂qSamplingLaw (qLbMDP γ (by linarith) hγ1) N = 0)) ∧
  ∃ c₃ : ℝ, 0 < c₃ ∧
  ∀ (γ : ℝ) (hγ : 3 / 4 ≤ γ) (hγ1 : γ < 1) (T : ℕ) (η : ℝ),
    c₃ / (1 - γ) ^ 2 ≤ T → 4 / ((1 - γ) * T) < η → η < 1 / ((1 - γ) ^ 2 * T) →
    let p : ℝ := (4 * γ - 1) / (3 * γ)
    let ρ : ℝ := 1 - η * (1 - γ * p)
    ∀ τhat : ℕ, ρ ^ (T + 1 - τhat) ≤ 6 / 7 →
      (∀ τ' : ℕ, ρ ^ (T + 1 - τ') ≤ 6 / 7 → τ' ≤ τhat) →
      ∀ t N : ℕ, τhat ≤ t → t ≤ N →
        0 < ∫ data, qLbXiMax γ η (qSamplesExtend (qLbMDP γ (by linarith) hγ1) N data) t
          ∂qSamplingLaw (qLbMDP γ (by linarith) hγ1) N

/-- Single-action synchronous Q-learning is TD learning: the identification behind sentence 3 of
Remark 4.5 (`chapters/generative_model_model_free.tex:3455–3457`, "when there is only a single
action ... leading respectively to `(1−γ)⁻³` and `(1−γ)⁻⁴`"). For a one-element action set
`{a}` (`Subsingleton Action`), every stationary policy `π` (necessarily the unique one) and every
learning-rate sequence: (i) pathwise, the synchronous Q-learning iterate at `a`
(`qLearningIterate`, Algorithm 4.2's update with `max` over actions) driven by next-state samples
`s'(t,s,a)` from `Q₀` equals the TD iterate (`tdIterate`) driven by the same samples from
`Q₀(·,a)`; (ii) in law, for every set `B` of value functions, the probability that `T` steps of
exact-`T` Q-learning output (read at `a`) lies in `B` equals the probability that `T` steps of
exact-`T` TD learning output lies in `B`; (iii) `Q⋆(s,a) = V^π(s)`. Hence the Q-learning error
event `|Q_T(s,a) − Q⋆(s,a)| ≤ ε` has exactly the probability of the TD error event of `Thm4_1`.
This entry does not itself restate the rates. -/
def QLearning_singleAction_eq_TD : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action] [Subsingleton Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) (a : Action)
    (η : ℕ → ℝ) (Q₀ : State → Action → ℝ),
    (∀ (samples : ℕ → State → Action → State) (t : ℕ) (s : State),
      qLearningIterate M η samples Q₀ t s a =
        tdIterate M π η (fun k s ↦ samples k s a) (fun s ↦ Q₀ s a) t s) ∧
    (∀ (T : ℕ) (B : Set (State → ℝ)),
      (qSamplingLaw M T).real {data | (fun s ↦ qSampledIterate M η T Q₀ data s a) ∈ B} =
        (tdSourceSamplingLaw M π T).real
          {data | tdSourceSampledIterate M π η T (fun s ↦ Q₀ s a) data ∈ B}) ∧
    (∀ s, M.trajectoryExpectedQ M.optimalGreedyPolicy s a = M.trajectoryExpectedValue π s)

/-- Corrected Theorem 4.13, `thm:finite-horizon-simple-Q-generative`,
`source/upstream/tex/chapters/generative_model_model_free.tex:2215–2236`, with the schedule
`eq:thm:finite-horizaon-eta` (`chapters/generative_model_model_free.tex:2205–2208`), the sample-size condition `eq:thm:finite-horizon-T`
(lines 2220–2223) and synchronous Q-learning `eqn:q-learning-finite` (`chapters/generative_model_model_free.tex:2175–2179`) with its
empirical Bellman operator (`chapters/generative_model_model_free.tex:2181–2200`).

The only change from the printed result is the premise `2 ≤ T`. The printed schedule divides by
`H log² T`, which is `0` at `T = 1`. Without the premise the Lean statement is false, not merely
ill-posed: at `T = 1` the junk values `Real.log 1 = 0` and `x / 0 = 0` force `η_1 = 1` and make the
sample-size condition `0 ≤ 1`, and a two-stage instance is never `1/4`-accurate
(`StatisticalRL.FiniteQLearning.not_thm4_13_from_one`). See
[`SOURCE-ISSUES.md#C35`](../../docs/SOURCE-ISSUES.md#C35).

"Sufficiently small universal constants `c₁ ≥ c₂ > 0`" and "sufficiently large `c₃`" are read as:
there is `c₀ > 0` such that every `0 < c₂ ≤ c₁ ≤ c₀` admits a universal `c₃ > 0`, chosen before the
model, `δ`, `ε` and `T`. Stage `h : Fin H` is the source step `h + 1`, so the initialization bound
`H + 1 - (h + 1)` is `H - h`. The terminal convention `Q_{t,H+1} ≡ 0`, left implicit in the source,
is built into `FiniteQLearning.sampledIterate`. Iteration `t` uses the `t`-th of the `T`
independent draws `s_{t,h}(s,a) ~ P_h(·|s,a)` of `FiniteHorizonGenerative.samplingLaw`. The
probability is strictly greater than `1 - δ`, as printed. Neither `A ≥ 2` nor `0 < η_t < 1` is
assumed. -/
def Thm4_13_corrected : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ c₂ : ℝ, 0 < c₂ → c₂ ≤ c₁ → c₁ ≤ c₀ → ∃ c₃ : ℝ, 0 < c₃ ∧
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H : ℕ) (E : Fin H → EnvironmentStage State Action) (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ),
    2 ≤ T → 0 < δ → δ < 1 → 0 < ε → ε ≤ 1 →
    (∀ t, t ≤ T →
      1 / (1 + c₁ * T / (H * Real.log (T : ℝ) ^ 2)) ≤ η t ∧
      η t ≤ 1 / (1 + c₂ * t / (H * Real.log (T : ℝ) ^ 2))) →
    c₃ * (H : ℝ) ^ 4 * Real.log (T : ℝ) ^ 3 *
      Real.log ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T / δ) / ε ^ 2 ≤ T →
    ∀ Q₀ : Fin H → State → Action → ℝ,
    (∀ h s a, 0 ≤ Q₀ h s a ∧ Q₀ h s a ≤ (H : ℝ) - h) →
    1 - δ < (FiniteHorizonGenerative.samplingLaw E T).real {data | ∀ h s a,
      |FiniteQLearning.sampledIterate E η T Q₀ data h s a -
        EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a| ≤ ε}

open Classical in
/-- Corrected Theorem 4.12, `thm:infinite-horizon-asyn`,
`chapters/generative_model_model_free.tex:2062–2086` (asynchronous Q-learning on one Markovian
trajectory), with the rate `eq:thm:infinite-horizaon-eta-asyn` (:2054–2058), the sampling model
(:1898–1906), the algorithm (:1928–1946, :1977–2001), `assump:ergodicity-asyncQ` (:2012–2015),
`defn:mu-min` (:2024–2028) and `defn-tmix` (:2034–2039). The monograph omits the proof (:2126);
the library proof is a new, self-contained argument.

Corrections (see `docs/SOURCE-ISSUES.md#C34`): the printed statement is false when `T = 1` and
`S A = 1` (then `log³T = 0`, `t_mix = 0`, the budget holds and the rate is `0`, so `Q_1 = Q_0`),
and when `μ_min = 0` (an unvisited pair is never updated). This entry adds `0 < μ_min` and the
weakest premise `2 ≤ T ∨ 2 ≤ S A` (with `S A ≥ 2` the budget already excludes `T = 1`).

`1 ≤ T` is a domain premise implicit in the source (the iterations run over `t = 1, …, T` and
`log T` must be defined); it is needed because at `T = 0` the budget collapses to `0 ≤ 0` through
Lean's `log 0 = 0`.

Reading: the probability is under the law of the state–action path `(s₀,a₀,…,s_T,a_T)` with mass
`1{s₀' = s₀} π_b(a₀|s₀) ∏_{i<T} P(s_{i+1}|s_i,a_i) π_b(a_{i+1}|s_{i+1})` (the finite marginal of the
trajectory of :1900–1903; `Q_T` only depends on it). Total variation is `½ ∑ |p - q|`; `t_mix` is
the least `t ∈ ℕ` (so `t_mix = 0` is allowed) with `max_{(s,a)} TV(P^t(·|s,a), μ) ≤ 1/4`;
uniform ergodicity is `TV(P^t(·|s,a), μ) ≤ C r^t` with `r < 1`; `μ` is a stationary distribution of
the pair chain; logarithms are natural. The printed "for some universal constants `0 < c₁ ≤ 1`"
(rate) and "sufficiently large `c₂`" (budget) are read as: for EVERY `c₁ ∈ (0,1]` there is a
universal `c₂ > 0` (depending only on `c₁`, chosen before the instance) such that the conclusion
holds. This is the strongest natural reading and implies the weaker `∃ c₁ ∃ c₂` reading. It is
proved by the library export `AsyncQ.asyncQ_exists_c₂` with `c₂ = max(e^{32/c₁}, 4096)`; `c₂`
growing like `e^{32/c₁}` is a proof artifact. The reversed order `∃ c₂ ∀ c₁` would be false. Fix
`c₂`, take `S = A = 1`,
`r = 1`, `γ = 1/2`, `Q₀ = 0` (so `Q⋆ = 2`) and any `T` satisfying the budget, which does not
involve `c₁`. Then the error `2(1-η)^T` tends to `2` as `c₁ → 0`. For example, `c₂ = 1.5·10⁵`,
`T = e^{40}` and `c₁ = 10⁻⁶` give an error of about `1.88 > 1`. This counterexample is a paper
computation and is not formalized.

Joint satisfiability of the budget for the chosen `c₂` is likewise argued on paper, not
machine-checked: for fixed instance parameters the right-hand side grows only polylogarithmically
in `T`, so every large enough `T` satisfies it. -/
def Thm4_12_corrected : Prop :=
  ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 → ∃ c₂ : ℝ, 0 < c₂ ∧
  ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A]
    (M : DiscountedMDP S A) (πb : StationaryPolicy S A) (μ : FiniteDistribution (S × A))
    (μmin : ℝ) (tmix : ℕ) (s₀ : S) (δ ε : ℝ) (T : ℕ),
    1 / 2 ≤ M.discount →
    (∀ y, ∑ x, μ.prob x * AsyncQ.pairKernel M πb x y = μ.prob y) →
    (∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ (t : ℕ) (x : S × A),
        FiniteMarkov.tvDist (AsyncQ.pairPow M πb t x) μ.prob ≤ C * r ^ t) →
    IsLeast {t : ℕ | ∀ x : S × A,
      FiniteMarkov.tvDist (AsyncQ.pairPow M πb t x) μ.prob ≤ 1 / 4} tmix →
    (∀ x, μmin ≤ μ.prob x) → (∃ x, μ.prob x = μmin) →
    0 < μmin → 1 ≤ T → (2 ≤ T ∨ 2 ≤ Fintype.card S * Fintype.card A) →
    0 < δ → δ < 1 → 0 < ε → ε ≤ 1 →
    c₂ * Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / δ) ^ 2 / μmin *
        max (Real.log T ^ 3 / ((1 - M.discount) ^ 4 * ε ^ 2)) (tmix / (1 - M.discount)) ≤ T →
    ∀ Q₀ : S → A → ℝ, (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
    1 - δ ≤ (AsyncQ.pathLaw M πb s₀ T).real {x | ∀ s a,
      |AsyncQ.iterate M (c₁ * Real.log T ^ 3 / ((1 - M.discount) * T * μmin)) Q₀ x T s a -
        M.trajectoryExpectedQ M.optimalGreedyPolicy s a| ≤ ε}


/-- Theorem 4.7, `thm:LB-example-Q-generative`, `chapters/generative_model_model_free.tex:969–982`,
as printed: both learning-rate schedules, (i) rescaled linear and (ii) constant.

Proof: case (ii) follows Appendix C (lines 2707–3944) as repaired in `docs/SOURCE-ISSUES.md#C31`
(the printed Freedman route of Lemma 4.15 and the closed form of Step 5.4 contain constant slips
and an off-by-one; only the unnamed constants are affected). For case (i) the source gives no
argument (line 2711 defers it to li2024q; `docs/SOURCE-ISSUES.md#C30`); the formal proof is new
(`QLearningLowerBoundRescaledTheorem.lean`). The exports use `c₃ = 16` and `c_lb = 10⁻⁹`.

Quantifiers: `c₃` and `c_lb` are universal (chosen first, independent of `γ`, `T`, `c_η`, `η₀`).
The schedule parameter (`c_η > 0` in case (i), `η₀ ∈ (0,1)` in case (ii)) is quantified after `γ`
and `T`, and the MDP after the schedule. The schedule is `η : ℕ → ℝ` with `η t` given for every
`t ≥ 0` as printed; `η 0` is never used, since round `t+1` of Algorithm `alg:q-infinite` (`chapters/generative_model_model_free.tex:841–870`;
`qLearningIterate`) uses `η (t+1)`.

Encoding (as for `Thm4_7_restricted`): `max_s E[|V_T(s) - V⋆(s)|²] ≥ b` is written
`∃ s, b ≤ E[…]` (finite state set). The MDP has `S = 4` states (`Fin 4`) and `A = 2` actions
(`Bool`) at every state, with rewards in `[0,1]` and discount `γ` (fields of `DiscountedMDP`).
`V_T` is the output of Algorithm `alg:q-infinite` (synchronous generative Q-learning,
`qSampledIterate`) after `T : ℕ` rounds from `Q₀ ≡ 0` under the genuine product sampling law
`qSamplingLaw M T`. `V⋆` is the trajectory value of the optimal greedy policy (the project
convention). `log` is the natural logarithm. The proof's witness is the source's `M_hard` with
dominated dummy actions at states 0, 2, 3 (`qLbMDP γ`, depending only on `γ`), since the source's
state-dependent action sets must be padded to two actions without changing the Q-learning
recursions (`docs/SOURCE-ISSUES.md#C31`, item 5). -/
def Thm4_7 : Prop :=
  ∃ c₃ c_lb : ℝ, 0 < c₃ ∧ 0 < c_lb ∧
  ∀ γ : ℝ, 3 / 4 ≤ γ → γ < 1 → ∀ T : ℕ, c₃ / (1 - γ) ^ 2 ≤ T →
  ∀ η : ℕ → ℝ,
    ((∃ cη : ℝ, 0 < cη ∧ ∀ t : ℕ, η t = 1 / (1 + cη * (1 - γ) * t)) ∨
      (∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧ ∀ t : ℕ, η t = η₀)) →
    ∃ M : DiscountedMDP (Fin 4) Bool, M.discount = γ ∧ ∃ s : Fin 4,
      c_lb / ((1 - γ) ^ 4 * T * Real.log T ^ 2) ≤
        ∫ data, (qLearningValue M (qSampledIterate M η T (fun _ _ ↦ 0) data) s -
          M.trajectoryExpectedValue M.optimalGreedyPolicy s) ^ 2 ∂qSamplingLaw M T

/-- Iteration-complexity reading of Theorem 4.7 (`thm:LB-example-Q-generative`),
`chapters/generative_model_model_free.tex:992–1000` (theorem :969–982): within the iteration
regime of Theorem 4.7 (`3/4 ≤ γ < 1`, `T ≥ c₃/(1−γ)²`) and for either learning-rate family
(rescaled linear with any `c_η > 0`, or constant `η₀ ∈ (0,1)`), there is an MDP with `S = 4`,
`A = 2` and discount `γ` on which plain Q-learning (from `Q₀ ≡ 0`) can reach mean-square accuracy
`max_s E|V_T(s) − V⋆(s)|² ≤ ε²` only if `T log² T ≥ c_lb/((1−γ)⁴ε²)`. The printed `Ω̃` is made
explicit by the `log² T` factor. `c₃` and `c_lb` are universal; the MDP is chosen after `γ`, `T`
and the schedule but before `ε`. Encoding of the objects as in `Thm4_7` (dummy actions per
`docs/SOURCE-ISSUES.md#C31` item 5; `V⋆` is the optimal greedy trajectory value). -/
def Thm4_7_iterationLowerBound : Prop :=
  ∃ c₃ c_lb : ℝ, 0 < c₃ ∧ 0 < c_lb ∧
  ∀ γ : ℝ, 3 / 4 ≤ γ → γ < 1 → ∀ T : ℕ, c₃ / (1 - γ) ^ 2 ≤ T →
  ∀ η : ℕ → ℝ,
    ((∃ cη : ℝ, 0 < cη ∧ ∀ t : ℕ, η t = 1 / (1 + cη * (1 - γ) * t)) ∨
      (∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧ ∀ t : ℕ, η t = η₀)) →
    ∃ M : DiscountedMDP (Fin 4) Bool, M.discount = γ ∧
      ∀ ε : ℝ, 0 < ε →
        (∀ s, ∫ data, (qLearningValue M (qSampledIterate M η T (fun _ _ ↦ 0) data) s -
            M.trajectoryExpectedValue M.optimalGreedyPolicy s) ^ 2 ∂qSamplingLaw M T ≤ ε ^ 2) →
        c_lb / ((1 - γ) ^ 4 * ε ^ 2) ≤ T * Real.log T ^ 2

/-- Theorem 4.7, `thm:LB-example-Q-generative`, `chapters/generative_model_model_free.tex:969–982`,
case (i) alone: rescaled linear learning rates `η_t = 1/(1 + c_η(1-γ)t)` for any `c_η > 0`.
Implied by `Thm4_7`; stated separately as a reading aid. The source gives no proof of this case
(`docs/SOURCE-ISSUES.md#C30`). `c₃`, `c_lb` are universal (independent of `c_η`); `c_η` is
quantified after `γ` and `T`. Encoding as for `Thm4_7` (dummy actions per
`docs/SOURCE-ISSUES.md#C31` item 5, `∃ s` for the max, `V⋆` = optimal greedy trajectory value,
natural log, `T : ℕ`, `Q₀ ≡ 0`, `η 0` unused). -/
def Thm4_7_case_i : Prop :=
  ∃ c₃ c_lb : ℝ, 0 < c₃ ∧ 0 < c_lb ∧
  ∀ γ : ℝ, 3 / 4 ≤ γ → γ < 1 → ∀ T : ℕ, c₃ / (1 - γ) ^ 2 ≤ T →
  ∀ cη : ℝ, 0 < cη →
    ∃ M : DiscountedMDP (Fin 4) Bool, M.discount = γ ∧ ∃ s : Fin 4,
      c_lb / ((1 - γ) ^ 4 * T * Real.log T ^ 2) ≤
        ∫ data, (qLearningValue M (qSampledIterate M (fun t ↦ 1 / (1 + cη * (1 - γ) * t)) T
          (fun _ _ ↦ 0) data) s -
          M.trajectoryExpectedValue M.optimalGreedyPolicy s) ^ 2 ∂qSamplingLaw M T

/-- Remark 4.1 (mean estimation guarantee for TD),
`chapters/generative_model_model_free.tex:226–239`, for Theorem 4.1 `thm:policy-evaluation-TD`
(:179–224). The constants `c₁, c₂, c₃` are those of Theorem 4.1: the statement quantifies them
existentially in the same order and with the same side conditions as `Thm4_1`, and the proof reuses
`Thm4_1`'s witnesses (`c₁ = c₂ = 1/4`, `c₃ = max(4096, e⁴/(log 2)⁴)`) by applying the same export
`tdSource_policyEvaluation_exactSamples_accuracy_exists_universal_constants`. `δ := ε(1−γ)/2` as
printed, so `S T/δ = 2 S T/(ε(1−γ))` and the budget is exactly Theorem 4.1's at this `δ`. `max_s` is
`⨆ s` over the finite nonempty state space. The expectation is the Bochner integral under the actual
sampling law of the `T` synchronous draws; integrability is concluded, not assumed (it excludes the
Bochner junk value). The five conjuncts are the printed `δ ∈ (0,1)`, the printed chain `E[…] ≤
ε(1−δ) + δ/(1−γ) ≤ 2ε`, and integrability. -/
def Remark4_1 : Prop :=
  ∃ c₁ c₂ c₃ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ 0 < c₃ ∧
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (ε : ℝ) (T : ℕ),
    1 / 2 ≤ M.discount → M.discount < 1 → 2 ≤ T →
    0 < ε → ε ≤ 1 / (1 - M.discount) →
    (∀ t, 1 ≤ t → t ≤ T →
      1 / (1 + c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 2) ≤ η t ∧
      η t ≤ 1 / (1 + c₂ * (1 - M.discount) * t / Real.log (T : ℝ) ^ 2)) →
    ∀ (V₀ : State → ℝ),
    (∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ 1 / (1 - M.discount)) →
    c₃ * Real.log (T : ℝ) ^ 3 *
      Real.log (2 * (Fintype.card State : ℝ) * T / (ε * (1 - M.discount))) /
        ((1 - M.discount) ^ 3 * ε ^ 2) ≤ (T : ℝ) →
    let δ := ε * (1 - M.discount) / 2
    let err := fun data ↦ ⨆ s : State,
      |tdSourceSampledIterate M π η T V₀ data s - M.trajectoryExpectedValue π s|
    0 < δ ∧ δ < 1 ∧
    Integrable err (tdSourceSamplingLaw M π T) ∧
    ∫ data, err data ∂(tdSourceSamplingLaw M π T) ≤
      ε * (1 - δ) + 1 / (1 - M.discount) * δ ∧
    ε * (1 - δ) + 1 / (1 - M.discount) * δ ≤ 2 * ε

/-- Remark 4.2 (mean estimation guarantee for synchronous Q-learning),
`chapters/generative_model_model_free.tex:914–929`, for Theorem 4.6 `thm:infinite-horizon-simple`
(:891–912). The constants are those of Theorem 4.6 (witnesses c₁ = c₂ = 1), quantified in the same
order and with the same
side conditions as `Thm4_6` (the proof reuses its witnesses by applying the same export
`qLearning_exists_universal_constants_source_accuracy`). `δ := ε(1−γ)/2` as printed, so
`S A T/δ = 2 S A T/(ε(1−γ))`. The premises other than `δ` are those of `Thm4_6`. `max_{(s,a)}` is
`⨆` over the finite nonempty pair space, `Q⋆` is the actual optimal trajectory Q-function (as in
`Thm4_6`), and the expectation is the Bochner integral under the actual product sampling law;
integrability is concluded. Five conjuncts as in `Remark4_1`. -/
def Remark4_2 : Prop :=
  ∃ c₁ c₂ c₃ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ 0 < c₃ ∧
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (η : ℕ → ℝ) (ε : ℝ) (T : ℕ),
    1/2 ≤ M.discount → 2 ≤ Fintype.card Action → 2 ≤ T →
    0 < ε → ε ≤ M.effectiveHorizon →
    (∀ k, k ≤ T →
      1 / (1 + c₁ * (1 - M.discount) * T / Real.log (T : ℝ) ^ 3) ≤ η k ∧
      η k ≤ 1 / (1 + c₂ * (1 - M.discount) * k / Real.log (T : ℝ) ^ 3)) →
    ∀ (Q₀ : State → Action → ℝ),
    (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
    c₃ * Real.log (T : ℝ)^4 * Real.log
      (2 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T /
        (ε * (1 - M.discount))) /
      ((1-M.discount)^4*ε^2) ≤ T →
    let δ := ε * (1 - M.discount) / 2
    let err := fun data ↦ ⨆ p : State × Action,
      |qSampledIterate M η T Q₀ data p.1 p.2 -
        M.trajectoryExpectedQ M.optimalGreedyPolicy p.1 p.2|
    0 < δ ∧ δ < 1 ∧
    Integrable err (qSamplingLaw M T) ∧
    ∫ data, err data ∂(qSamplingLaw M T) ≤ ε * (1 - δ) + 1 / (1 - M.discount) * δ ∧
    ε * (1 - δ) + 1 / (1 - M.discount) * δ ≤ 2 * ε

open Classical in
/-- Corrected Remark 4.3, `chapters/generative_model_model_free.tex:2088–2090`, for Theorem 4.12
`thm:infinite-horizon-asyn` (:2062–2086, asynchronous Q-learning). The printed remark has no
displayed formula: it says the
high-probability result "can be readily translated into a bound on the expected ℓ∞-based
estimation error with essentially the same sample complexity" and omits the details. The precise
reading (confirmed by the independent plan check) mirrors Remarks 4.1/4.2 ("As before"):
`δ := ε(1−γ)/2` inside Theorem 4.12's budget, so `S A T/δ = 2 S A T/(ε(1−γ))`, and
`E[max_{(s,a)} |Q_T − Q⋆|] ≤ ε(1−δ) + δ/(1−γ) ≤ 2ε`, with fresh universal constants
`∃ c₁ ∈ (0,1], ∃ c₂ > 0` in the order of `Thm4_12_corrected` (enlarging `c₂` is within
"essentially the same").

Correction (`docs/SOURCE-ISSUES.md#C34`): under Theorem 4.12's printed premises this reading is
false, as Theorem 4.12 itself is. Take `S = A = 1`, `γ = 1/2`, `r = 1`, `Q₀ = 0` (so `Q⋆ = 2`),
`μ_min = 1`, `t_mix = 0`, `T = 1`, `ε = 1/2` (`δ = 1/8`): `log³ T = 0`, so the budget reads `0 ≤ 1`
and the rate is `0`, hence `Q₁ = Q₀` and the mean error is `2 > 1 = 2ε`. This counterexample is a
paper computation and is not formalized; the independent critic machine-checked only its pieces
(at `T = 1` the rate is `0`, a zero rate leaves every `AsyncQ.iterate` equal to `Q₀`, and the budget
holds for every `c₂`), not `Q⋆ = 2` or the expectation. (Read with `η_t ∈ (0,1)`
from :1951 the instance is ill-posed, as noted in C34(1).) If `μ_min = 0` an unvisited pair keeps
`Q₀ ≠ Q⋆` forever and the mean error can exceed `2ε` (C34(2)). This entry therefore carries
exactly the C34 premises of `Thm4_12_corrected`: `0 < μ_min`, `1 ≤ T`, `2 ≤ T ∨ 2 ≤ S A`,
stationarity, uniform ergodicity, `IsLeast … t_mix`, `μ_min` attained, `ε ≤ 1`. The path law,
total variation, `t_mix` and the rate `c₁ log³T/((1−γ) T μ_min)` are as in `Thm4_12_corrected`. The
expectation is the Bochner integral under the path law; integrability is concluded. -/
def Remark4_3_corrected : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧ ∃ c₂ : ℝ, 0 < c₂ ∧
  ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A]
    (M : DiscountedMDP S A) (πb : StationaryPolicy S A) (μ : FiniteDistribution (S × A))
    (μmin : ℝ) (tmix : ℕ) (s₀ : S) (ε : ℝ) (T : ℕ),
    1 / 2 ≤ M.discount →
    (∀ y, ∑ x, μ.prob x * AsyncQ.pairKernel M πb x y = μ.prob y) →
    (∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ (t : ℕ) (x : S × A),
        FiniteMarkov.tvDist (AsyncQ.pairPow M πb t x) μ.prob ≤ C * r ^ t) →
    IsLeast {t : ℕ | ∀ x : S × A,
      FiniteMarkov.tvDist (AsyncQ.pairPow M πb t x) μ.prob ≤ 1 / 4} tmix →
    (∀ x, μmin ≤ μ.prob x) → (∃ x, μ.prob x = μmin) →
    0 < μmin → 1 ≤ T → (2 ≤ T ∨ 2 ≤ Fintype.card S * Fintype.card A) →
    0 < ε → ε ≤ 1 →
    c₂ * Real.log (2 * (Fintype.card S : ℝ) * Fintype.card A * T /
          (ε * (1 - M.discount))) ^ 2 / μmin *
        max (Real.log T ^ 3 / ((1 - M.discount) ^ 4 * ε ^ 2)) (tmix / (1 - M.discount)) ≤ T →
    ∀ Q₀ : S → A → ℝ, (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ M.effectiveHorizon) →
    let δ := ε * (1 - M.discount) / 2
    let err := fun x ↦ ⨆ p : S × A,
      |AsyncQ.iterate M (c₁ * Real.log T ^ 3 / ((1 - M.discount) * T * μmin)) Q₀ x T p.1 p.2 -
        M.trajectoryExpectedQ M.optimalGreedyPolicy p.1 p.2|
    0 < δ ∧ δ < 1 ∧
    Integrable err (AsyncQ.pathLaw M πb s₀ T) ∧
    ∫ x, err x ∂(AsyncQ.pathLaw M πb s₀ T) ≤ ε * (1 - δ) + 1 / (1 - M.discount) * δ ∧
    ε * (1 - δ) + 1 / (1 - M.discount) * δ ≤ 2 * ε

end StatisticalRL.Statements.Ch4
