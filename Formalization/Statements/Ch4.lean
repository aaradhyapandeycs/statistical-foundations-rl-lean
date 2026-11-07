import Formalization.ModelFree.QLearningHardMDPDefinitions
import Formalization.ModelFree.QLearningLowerBoundDefinitions
import Formalization.ModelFree.TDConditionalMomentDefinitions
import Formalization.ModelFree.TDSourceFixedTerminalProxyDefinitions
import Formalization.ModelFree.TDSourceSamplingDefinitions
import Formalization.ModelFree.QLearningSamplingDefinitions
import Formalization.ModelFree.QLearningComparisonDefinitions
import Formalization.ModelFree.QLearningRobustDefinitions
import Formalization.ModelFree.FiniteQ.Definitions

/-! Source-facing statement index for Chapter 4. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.Statements.Ch4
open StatisticalRL.TemporalDifference StatisticalRL.QLearning
universe u v
local instance stateMeasurable (State : Type*) : MeasurableSpace State := ⊤
local instance actionMeasurable (Action : Type*) : MeasurableSpace Action := ⊤

/-- `thm:policy-evaluation-TD`, `chapters/generative_model_model_free.tex:179–224`.
The proof uses the universal witness `c₁=c₂=1/4` and
`c₃=max(4096, exp(4)/(log 2)^4)`. The indexed event uses exactly the source's
T synchronous samples and compares the resulting iterate with the true
infinite-trajectory policy value. -/
def Thm4_1 : Prop :=
  ∃ c₁ c₂ c₃ : ℝ, 0 < c₂ ∧ c₂ ≤ c₁ ∧ 0 < c₃ ∧
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
/-- Corrected Lemma 4.3, `lemma:TD-step-size`, `chapters/generative_model_model_free.tex:317–327`,
with the schedule `eq:thm:eta-TD` (lines 182–184) and the weights `η_k^{(t)}` of
`def:eta-k-t` (lines 307–313) written out (the `k = 0` branch takes precedence at `t = 0`).

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
the learning-rate schedule `eq:thm:infinite-horizaon-eta` (lines 882–886), with
`η̄ = min{1, 2 log³T / (c₂(1-γ)T)}` of `eq:Q-comparison-parameters` (lines 1087–1089) and the
weights `η_i^{(t)}` of `def:eta-i-t-simple` (lines 1075–1083) written out; the `i = 0` branch
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

Restriction: only case (ii), constant learning rates `η_t ≡ η ∈ (0,1)`, is stated and proved.
Case (i) (rescaled linear rates `η_t = 1/(1 + c_η(1-γ)t)`) is not proved in the source (it is
deferred to li2024q) and remains an open obligation; see `docs/SOURCE-ISSUES.md#C30`.

Encoding: `max_s E[|V_T(s) - V⋆(s)|²] ≥ b` is written `∃ s, b ≤ E[…]` (finite state set). The
MDP has `S = 4` states (`Fin 4`) and `A = 2` actions (`Bool`) at every state, with rewards in
`[0,1]` and discount `γ` (fields of `DiscountedMDP`). `V_T` is the output of Algorithm
`alg:q-infinite` (synchronous generative Q-learning, `qSampledIterate`) after `T` rounds from
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
`eqn:defn-xi-t`, lines 3405–3411) is built from the auxiliary sequence `Q̂_t` (`qLbAuxIterate`,
`eqn:Qhat-schumann`, lines 3316–3324, initialized at `Q⋆(1,a) = 1/(1-γp)`) driven by the state-1
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

/-- Corrected Theorem 4.13, `thm:finite-horizon-simple-Q-generative`,
`source/upstream/tex/chapters/generative_model_model_free.tex:2215–2236`, with the schedule
`eq:thm:finite-horizaon-eta` (lines 2203–2209), the sample-size condition `eq:thm:finite-horizon-T`
(lines 2220–2223) and synchronous Q-learning `eqn:q-learning-finite` with its empirical Bellman
operator (lines 2181–2200).

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

end StatisticalRL.Statements.Ch4
