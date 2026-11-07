import Formalization.Ch7Rest.FedPrinted79
import Formalization.MDP.FixedPointDefinitions
import Formalization.Probability.FiniteSampleDefinitions

/-!
# The generic federated Q-learning algorithm with intermittent communication (definitions only)

Source: `chapters/federated_RL.tex`, Algorithm `alg:general_fed_alg_with_inter_comm`
(generic algorithm `𝒜`) :166–220 (algorithm box :200–220), used by Theorem 7.10
(`thm:lower_bound`) :227–239.

This file only defines objects; it proves nothing.

* `batchUpdate` is the minibatch Q-learning update `eqn:generic_algo_update` (:186–188): with
  `B` sampled next states `s'_b ∼ P(·|s,a)`, the sample Bellman operator is
  `𝒯̂_b(Q)(s,a) = r(s,a) + γ max_{a'} Q(s'_b, a')` and
  `Q_{t-1/2} = (1 - η_t) Q_{t-1} + (η_t / B) ∑_b 𝒯̂_b(Q_{t-1})`.
* `genericStep` is the synchronization `eqn:generic_algo_averaging` (:191–194): exact averaging
  over the `K` agents when `t ∈ 𝒞`, no change otherwise. Only exact averaging is modelled: the
  sentence at :196 allowing the averaging to be replaced by "any distributed mean estimation
  routine" (including compressed variants) is not covered.
* `genericRun` starts from `Q_0^k = 0` (:207) and runs the iterations `t = 1, 2, …`.
* `genericOutput` is `Q̂ = Q_T`, written as the agent average `(1/K) ∑_k Q_T^k`; when `T ∈ 𝒞`
  (the source's standing assumption `t_{C_round} = T`, :196) all agents hold the same iterate,
  so this is every agent's `Q_T^k`.
* `fedSamplingLaw` is the genuine product law: for every iteration `t ∈ {1,…,T}` (index `t-1`),
  agent `k`, pair `(s,a)` and batch slot `b`, one independent draw from `P(·|s,a)` (:183–184).
* `supError` is `‖Q - Q'‖_∞` over the finite state-action set.
* `Thm7_10_innerConstant` is printed Theorem 7.10 under the reading with `c₀` inside the
  hypothesis (false; refuted in `Formalization/Ch7Rest/InnerConstant710.lean`).
-/

open MeasureTheory

namespace StatisticalRL.Ch7Rest.FedGeneric

open StatisticalRL.Ch7Rest.Fed (greedyValue)

variable {State Action : Type} [Fintype State] [Fintype Action]

/-- Minibatch local Q-learning update `eqn:generic_algo_update` (`federated_RL.tex:186–188`)
with sampled next states `next s a b = s'_b(s,a)`, `b ∈ Fin B`. -/
noncomputable def batchUpdate (M : DiscountedMDP State Action) (η : ℝ) (B : ℕ)
    (Q : State → Action → ℝ) (next : State → Action → Fin B → State) : State → Action → ℝ :=
  fun s a ↦ (1 - η) * Q s a +
    η / (B : ℝ) * ∑ b, (M.reward s a + M.discount * greedyValue Q (next s a b))

/-- One iteration `t` of the generic algorithm (`federated_RL.tex:183–194`): local minibatch
updates of all `K` agents, then exact averaging when `t ∈ 𝒞`. -/
noncomputable def genericStep (M : DiscountedMDP State Action) (η : ℝ) (K B : ℕ)
    (𝒞 : Finset ℕ) (t : ℕ) (Qs : Fin K → State → Action → ℝ)
    (next : Fin K → State → Action → Fin B → State) : Fin K → State → Action → ℝ :=
  if t ∈ 𝒞 then fun _ s a ↦ (1 / (K : ℝ)) * ∑ j, batchUpdate M η B (Qs j) (next j) s a
  else fun k ↦ batchUpdate M η B (Qs k) (next k)

/-- Local iterates `Q_t^k` of the generic algorithm `𝒜` (`federated_RL.tex:200–220`) with
learning rates `η t = η_t`, started from `Q_0^k = 0`, along a sample path
`samples t k s a b` (the `b`-th draw for `(s,a)` by agent `k` at iteration `t`). -/
noncomputable def genericRun (M : DiscountedMDP State Action) (η : ℕ → ℝ) (K B : ℕ)
    (𝒞 : Finset ℕ) (samples : ℕ → Fin K → State → Action → Fin B → State) :
    ℕ → Fin K → State → Action → ℝ
  | 0 => fun _ _ _ ↦ 0
  | t + 1 => genericStep M (η (t + 1)) K B 𝒞 (t + 1) (genericRun M η K B 𝒞 samples t)
      (samples (t + 1))

/-- Output `Q̂ = Q_T` (`federated_RL.tex:219`), as the agent average `(1/K) ∑_k Q_T^k`. -/
noncomputable def genericOutput (M : DiscountedMDP State Action) (η : ℕ → ℝ) (K B : ℕ)
    (𝒞 : Finset ℕ) (samples : ℕ → Fin K → State → Action → Fin B → State) (T : ℕ) :
    State → Action → ℝ :=
  fun s a ↦ (1 / (K : ℝ)) * ∑ k, genericRun M η K B 𝒞 samples T k s a

/-- Sample coordinates: (iteration index `t-1`, agent), (state, action), batch slot. -/
abbrev FedIndex (State Action : Type) (T K B : ℕ) := (Fin T × Fin K) × (State × Action) × Fin B

/-- One realization of all next-state draws of a run of length `T`. -/
abbrev FedSamples (State Action : Type) (T K B : ℕ) := FedIndex State Action T K B → State

local instance fedGenericStateMeasurable : MeasurableSpace State := ⊤

/-- The genuine product sampling law: all draws independent, the draw for `(s,a)` from the
actual transition row `P(·|s,a)` (`federated_RL.tex:183–184`). -/
noncomputable def fedSamplingLaw (M : DiscountedMDP State Action) (T K B : ℕ) :
    Measure (FedSamples State Action T K B) :=
  Measure.pi (fun i : FedIndex State Action T K B ↦ (M.transition i.2.1.1 i.2.1.2).rowMeasure)

/-- Iteration `t ∈ {1,…,T}` uses coordinate `t-1`; outside that range a fixed state is
returned, which iterations `≤ T` never query. -/
noncomputable def fedSamplesExtend (M : DiscountedMDP State Action) (T K B : ℕ)
    (data : FedSamples State Action T K B) : ℕ → Fin K → State → Action → Fin B → State :=
  fun t k s a b ↦
    if h : 0 < t ∧ t ≤ T then data ((⟨t - 1, by omega⟩, k), (s, a), b)
    else Classical.choice M.state_nonempty

/-- `‖Q - Q'‖_∞ = max_{s,a} |Q(s,a) - Q'(s,a)|` over the finite state-action set. -/
noncomputable def supError (Q Q' : State → Action → ℝ) : ℝ :=
  ⨆ s, ⨆ a, |Q s a - Q' s a|

/-- Theorem 7.10, `thm:lower_bound`, `chapters/federated_RL.tex:227–239`, under the alternative
reading in which "for some universal constant `c₀ > 0`" sits inside the hypothesis:
"if there is some `c₀ > 0` with `C_round ≤ c₀ / ((1-γ) log² N)`, then …". All other quantifiers
and objects are as in the statement-index entry `Thm7_10` (universal `c₀` first). This reading
is false (`docs/SOURCE-ISSUES.md#C42`): since
`N ≥ 16`, the hypothesis always holds, and full synchronization with many agents makes the
expected error exponentially small in `T`. Refuted by `not_thm7_10_innerConstant` in
`Formalization/Ch7Rest/InnerConstant710.lean`. The learning-rate schedule is constrained only
on `1 ≤ t ≤ T`, as printed. -/
def Thm7_10_innerConstant : Prop :=
  ∃ Cγ : ℝ → ℝ, ∀ γ : ℝ, 5 / 6 ≤ γ → γ < 1 → 0 < Cγ γ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action],
      4 ≤ Fintype.card State → 2 ≤ Fintype.card Action →
      ∀ (T B : ℕ) (𝒞 : Finset ℕ) (η : ℕ → ℝ),
        16 ≤ T → 1 / (1 - γ) ≤ (T : ℝ) → 1 ≤ B →
        𝒞 ⊆ Finset.Icc 1 T → T ∈ 𝒞 →
        ((∃ c_η : ℝ, 0 < c_η ∧ ∀ t : ℕ, 1 ≤ t → t ≤ T → η t = 1 / (1 + c_η * (1 - γ) * t)) ∨
          (∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧ ∀ t : ℕ, 1 ≤ t → t ≤ T → η t = η₀)) →
        (∃ c₀ : ℝ, 0 < c₀ ∧ (𝒞.card : ℝ) ≤ c₀ / ((1 - γ) * Real.log ((B : ℝ) * T) ^ 2)) →
        ∃ M : DiscountedMDP State Action, M.discount = γ ∧
          ∀ K : ℕ, 2 ≤ K →
            Cγ γ / (Real.sqrt ((B : ℝ) * T) * Real.log ((B : ℝ) * T) ^ 3) ≤
              ∫ data, supError (genericOutput M η K B 𝒞 (fedSamplesExtend M T K B data) T)
                M.optimalityFixedPoint ∂fedSamplingLaw M T K B

end StatisticalRL.Ch7Rest.FedGeneric
