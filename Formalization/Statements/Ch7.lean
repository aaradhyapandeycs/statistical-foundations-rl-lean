import Formalization.RobustRL.TVWeakDefinitions
import Formalization.ModelFree.QLearningRobustDefinitions
import Formalization.Ch7Rest.FedGeneric710
import Formalization.RobustRL.Ch7.Ch7Definitions
import Formalization.Ch7Rest.Marl78Defs
import Formalization.Ch7Rest.VPODefs712
import Formalization.Ch7Rest.Marl76Defs
import Formalization.Ch7Rest.TDInference711Defs
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.CDF

/-! Full source-facing statement of robust_RL.tex:302–324, label
`lemma:dual-form`.  The two source choices of discrepancy are recorded as
separate conjuncts, with the finite feasible-row sets expanded below. -/

open scoped BigOperators
namespace StatisticalRL.Statements.Ch7
universe u

/-- TV projection of the complete `Lemma7_1` below, `lemma:dual-form`,
`chapters/robust_RL.tex:302–324`. Finite event TV is represented by its
equivalent half-L1 distance. -/
noncomputable def Lemma7_1_tv : Prop :=
  ∀ (State : Type u) [Fintype State] [Nonempty State]
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ) (σ : ℝ),
    0 < σ → (∀ s, 0 ≤ V s) →
    ∃ α ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty V)
        (Finset.univ.sup' Finset.univ_nonempty V),
      (⨅ q : {q : StatisticalRL.FiniteDistribution State //
          (1 / 2 : ℝ) * ∑ s, |p.prob s - q.prob s| ≤ σ},
        ∑ s, q.1.prob s * V s) =
        (∑ s, p.prob s * min (V s) α) - σ *
          (α - Finset.univ.inf' Finset.univ_nonempty (fun s ↦ min (V s) α)) ∧
      ∀ β ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty V)
          (Finset.univ.sup' Finset.univ_nonempty V),
        (∑ s, p.prob s * min (V s) β) - σ *
          (β - Finset.univ.inf' Finset.univ_nonempty (fun s ↦ min (V s) β)) ≤
        (∑ s, p.prob s * min (V s) α) - σ *
          (α - Finset.univ.inf' Finset.univ_nonempty (fun s ↦ min (V s) α))

attribute [local instance] Classical.propDecidable

/-- `lemma:dual-form`, `chapters/robust_RL.tex:302–324`: both the total
variation and χ² branches of the source finite-row strong-duality statement.
For the χ² branch the Pearson sum is restricted to positive nominal atoms and
feasibility separately forces zero mass on nominal zero atoms. -/

noncomputable def Lemma7_1 : Prop :=
  ∀ (State : Type u) [Fintype State] [Nonempty State]
    (p : StatisticalRL.FiniteDistribution State) (V : State → ℝ) (σ : ℝ),
    0 < σ → (∀ s, 0 ≤ V s) →
    (∃ α ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty V)
        (Finset.univ.sup' Finset.univ_nonempty V),
      (⨅ q : {q : StatisticalRL.FiniteDistribution State //
          (1 / 2 : ℝ) * ∑ s, |p.prob s - q.prob s| ≤ σ},
        ∑ s, q.1.prob s * V s) =
        (∑ s, p.prob s * min (V s) α) - σ *
          (α - Finset.univ.inf' Finset.univ_nonempty (fun s ↦ min (V s) α)) ∧
      ∀ β ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty V)
          (Finset.univ.sup' Finset.univ_nonempty V),
        (∑ s, p.prob s * min (V s) β) - σ *
          (β - Finset.univ.inf' Finset.univ_nonempty (fun s ↦ min (V s) β)) ≤
        (∑ s, p.prob s * min (V s) α) - σ *
          (α - Finset.univ.inf' Finset.univ_nonempty (fun s ↦ min (V s) α))) ∧
    (∃ α ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty V)
        (Finset.univ.sup' Finset.univ_nonempty V),
      (sInf {z : ℝ | ∃ q : StatisticalRL.FiniteDistribution State,
          (∀ s, p.prob s = 0 → q.prob s = 0) ∧
          (∑ s ∈ Finset.univ.filter (fun s ↦ 0 < p.prob s),
            (q.prob s - p.prob s) ^ 2 / p.prob s) ≤ σ ∧
          z = ∑ s, q.prob s * V s}) =
        (∑ s, p.prob s * min (V s) α) - Real.sqrt (σ *
          ((∑ s, p.prob s * (min (V s) α) ^ 2) -
            (∑ s, p.prob s * min (V s) α) ^ 2)) ∧
      ∀ β ∈ Set.Icc (Finset.univ.inf' Finset.univ_nonempty V)
          (Finset.univ.sup' Finset.univ_nonempty V),
        (∑ s, p.prob s * min (V s) β) - Real.sqrt (σ *
          ((∑ s, p.prob s * (min (V s) β) ^ 2) -
            (∑ s, p.prob s * min (V s) β) ^ 2)) ≤
        (∑ s, p.prob s * min (V s) α) - Real.sqrt (σ *
          ((∑ s, p.prob s * (min (V s) α) ^ 2) -
            (∑ s, p.prob s * min (V s) α) ^ 2)))


open MeasureTheory StatisticalRL.Ch7Rest.FedGeneric in
/-- Theorem 7.10, restricted, `thm:lower_bound`, `chapters/federated_RL.tex:227–239` (generic algorithm
`alg:general_fed_alg_with_inter_comm`, `chapters/federated_RL.tex:166–220`, box `chapters/federated_RL.tex:200–220`), read with the universal
constant `c₀` quantified first: "there is a universal constant `c₀ > 0` such that, if
`C_round ≤ c₀ / ((1-γ) log² N)`, then …".

Every printed hypothesis is written out: `γ ∈ [5/6, 1)`, `S ≥ 4`, `A ≥ 2`,
`T ≥ max{16, 1/(1-γ)}`, the two learning-rate schedules (`η_t = 1/(1 + c_η(1-γ)t)` with
`c_η > 0`, or `η_t = η ∈ (0,1)`), constrained only for `1 ≤ t ≤ T` as printed, any
communication schedule `𝒞 = {t_r} ⊆ {1,…,T}` with the source's standing assumption
`t_{C_round} = T` (line 196), `C_round = |𝒞|`, any batch size `B ≥ 1`, and `N = BT` (line 196).
`C_γ` is a function of `γ` alone (`c₀` is a fixed number), chosen before everything except `γ`.
The MDP instance has state set `State` (`S = |State|`), action set `Action`, discount `γ`,
rewards in `[0,1]`, and is chosen before the number of agents `K ≥ 2`. `Q̂` is the output of
Algorithm 𝒜 (`genericOutput`: update lines 186–188, averaging at `t ∈ 𝒞` lines 191–194,
`Q_0 = 0` line 207, return line 219). Restriction (hence the `_restricted` name,
`docs/SOURCE-ISSUES.md#C42`): line 196 puts any distributed mean-estimation routine (including
compressed variants) in the generic algorithm class; only exact averaging is modelled, so the
lower bound is proved for that sub-class only and other mean-estimation routines are not covered. The expectation is over the genuine independent generative sampling law
`fedSamplingLaw` (lines 183–184), `Q⋆` is the unique solution of the Bellman optimality equation
(`optimalityFixedPoint`), `‖·‖_∞` is the max over state-action pairs (`supError`), and `log` is
the natural logarithm.

Reading and source issue (`docs/SOURCE-ISSUES.md#C42`): since `T ∈ 𝒞`, `C_round ≥ 1`, so the
hypothesis forces `log² N ≤ c₀/(1-γ)`. Disclosure: the bound is proved with
`C_γ = γ^{⌊exp √(c₀/(1-γ))⌋} / (1-γ)`, which is doubly exponentially small; the library export
`lowerBound_of_fewRounds` holds for every `c₀` (this entry uses `c₀ = 1`). The result does not
establish the discussion at lines 242–248 (a communication requirement of order `1/(1-γ)`).
Under the other reading ("for some `c₀ > 0`" inside the hypothesis) the hypothesis is vacuous
and the statement is false: see `StatisticalRL.Ch7Rest.FedGeneric.Thm7_10_innerConstant`,
refuted by `StatisticalRL.Ch7Rest.FedGeneric.not_thm7_10_innerConstant`. -/
def Thm7_10_restricted : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ Cγ : ℝ → ℝ, ∀ γ : ℝ, 5 / 6 ≤ γ → γ < 1 → 0 < Cγ γ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action],
      4 ≤ Fintype.card State → 2 ≤ Fintype.card Action →
      ∀ (T B : ℕ) (𝒞 : Finset ℕ) (η : ℕ → ℝ),
        16 ≤ T → 1 / (1 - γ) ≤ (T : ℝ) → 1 ≤ B →
        𝒞 ⊆ Finset.Icc 1 T → T ∈ 𝒞 →
        ((∃ c_η : ℝ, 0 < c_η ∧ ∀ t : ℕ, 1 ≤ t → t ≤ T → η t = 1 / (1 + c_η * (1 - γ) * t)) ∨
          (∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < 1 ∧ ∀ t : ℕ, 1 ≤ t → t ≤ T → η t = η₀)) →
        (𝒞.card : ℝ) ≤ c₀ / ((1 - γ) * Real.log ((B : ℝ) * T) ^ 2) →
        ∃ M : DiscountedMDP State Action, M.discount = γ ∧
          ∀ K : ℕ, 2 ≤ K →
            Cγ γ / (Real.sqrt ((B : ℝ) * T) * Real.log ((B : ℝ) * T) ^ 3) ≤
              ∫ data, supError (genericOutput M η K B 𝒞 (fedSamplesExtend M T K B data) T)
                M.optimalityFixedPoint ∂fedSamplingLaw M T K B

section Thm7_3

/-- Every finite carrier gets the discrete σ-algebra (as in the printed transcriptions of
`Formalization/RobustRL/Ch7/Ch7PrintedStatements.lean`); the generative sampling law is the
product of the nominal rows over all `((s,a), i)`. -/
local instance ch7StatementStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

open StatisticalRL StatisticalRL.RobustRL.Ch7 in
/-- Corrected Theorem 7.3, `thm:l1-lower-bound`, `chapters/robust_RL.tex:377–391` (TV-robust
MDP `:19–157`, generative sampling `:135–147`, `:206–215`), corrected by adding the single
hypothesis `A ≥ 2` (`docs/SOURCE-ISSUES.md#C38`: the printed result is false at `A = 1`).
For every constant `0 < c₀ ≤ 1/8`, all `S` (the state type), `A ≥ 2`, `σ ∈ (0, 1-c₀]`,
`γ ∈ [1/2, 1)`, `ε ∈ (0, c₀/(256(1-γ))]` and `N ≤ c₀ log 2 / (8192 (1-γ)² max(1-γ,σ) ε²)`,
there are two RMDPs `M₀, M₁` on the given states and actions (discount `γ`, rewards in
`[0,1]`, `(s,a)`-rectangular TV balls of radius `σ` around the nominal kernel) and an initial
distribution `μ` such that every estimator (a map from the `N` samples per state-action pair
to a stationary randomized policy) has `max_i P_i(V_i^{⋆,σ}(μ) - V_i^{π̂,σ}(μ) > ε) ≥ 1/8`.
Here an estimator is a deterministic function of the samples; estimators with an independent random
seed are covered by `Thm7_3_corrected_randomized`, of which this entry is the `Ω = Unit` case.

Disclosure on the estimator class. `M₀` and `M₁` may have different rewards, and the
estimators see the samples only, not the reward.
* The `S = 1` case holds only because the estimators cannot see the reward (proof: a shared
  self-loop kernel with rewards `1[a = a_j]`). Under the book's known-reward convention
  (`generative_model_model_based.tex:31`; `robust_RL.tex:25`, `robust_RL.tex:206–215`) the
  printed claim is false at `S = 1`: with one state the data are uninformative, the reward is
  known, and `argmax r` is robust-optimal (C38).
* For `S ≥ 2` the proof uses two models with one shared reward that differ only in the
  nominal rows at `(s₀, a₀)` and `(s₀, a₁)`; the known-reward reading is `Thm7_3_corrected_knownReward`. -/
def Thm7_3_corrected : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 8 →
  ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
    [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
    2 ≤ Fintype.card Action →
    0 < σ → σ ≤ 1 - c₀ → 1 / 2 ≤ γ → γ < 1 → 0 < ε → ε ≤ c₀ / (256 * (1 - γ)) →
    (N : ℝ) ≤ c₀ * Real.log 2 / (8192 * (1 - γ) ^ 2 * max (1 - γ) σ * ε ^ 2) →
    ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
      M₀.discount = γ ∧ M₁.discount = γ ∧
      ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
        1 / 8 ≤ max
          ((ModelBasedPolicyLearning.samplingLaw M₀ N).real
            {data | ε < robustOptimalValueAt tvBall M₀ σ μ -
              robustPolicyValueAt tvBall M₀ σ (est data) μ})
          ((ModelBasedPolicyLearning.samplingLaw M₁ N).real
            {data | ε < robustOptimalValueAt tvBall M₁ σ μ -
              robustPolicyValueAt tvBall M₁ σ (est data) μ})

open StatisticalRL StatisticalRL.RobustRL.Ch7 in
/-- Corrected Theorem 7.3 under the book's known-reward convention: `thm:l1-lower-bound`,
`chapters/robust_RL.tex:377–391`, read with the convention that the reward is known to the
learner (`generative_model_model_based.tex:31`; `robust_RL.tex:25`, `robust_RL.tex:206–215`),
encoded by requiring the two RMDPs to share their reward (`M₀.reward = M₁.reward`), so that
only the nominal kernel is unknown. This is the faithful reading of the printed result under
that convention. It is corrected by adding the hypotheses `S ≥ 2` and `A ≥ 2`
(`docs/SOURCE-ISSUES.md#C38`): both are needed there, since `A = 1` is refuted in Lean (for the printed statement, which this conclusion implies) and
`S = 1` makes the printed claim false under known rewards (paper argument, not machine-checked:
`argmax r` is then robust-optimal). Every other constant, range and the conclusion are
as printed (see `Thm7_3_corrected`). The two models of the proof differ only in the nominal
rows at `(s₀, a₀)` and `(s₀, a₁)`. Estimators here are deterministic functions of the samples;
seeded randomized estimators are covered by `Thm7_3_corrected_knownReward_randomized`. -/
def Thm7_3_corrected_knownReward : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 8 →
  ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
    [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
    2 ≤ Fintype.card State → 2 ≤ Fintype.card Action →
    0 < σ → σ ≤ 1 - c₀ → 1 / 2 ≤ γ → γ < 1 → 0 < ε → ε ≤ c₀ / (256 * (1 - γ)) →
    (N : ℝ) ≤ c₀ * Real.log 2 / (8192 * (1 - γ) ^ 2 * max (1 - γ) σ * ε ^ 2) →
    ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
      M₀.discount = γ ∧ M₁.discount = γ ∧ M₀.reward = M₁.reward ∧
      ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
        1 / 8 ≤ max
          ((ModelBasedPolicyLearning.samplingLaw M₀ N).real
            {data | ε < robustOptimalValueAt tvBall M₀ σ μ -
              robustPolicyValueAt tvBall M₀ σ (est data) μ})
          ((ModelBasedPolicyLearning.samplingLaw M₁ N).real
            {data | ε < robustOptimalValueAt tvBall M₁ σ μ -
              robustPolicyValueAt tvBall M₁ σ (est data) μ})

open StatisticalRL StatisticalRL.RobustRL.Ch7 MeasureTheory in
/-- Corrected Theorem 7.3 for externally randomized estimators, `thm:l1-lower-bound`,
`chapters/robust_RL.tex:377–391` (the printed infimum is over all estimators, `:389`). It extends
`Thm7_3_corrected` (same constants `0 < c₀ ≤ 1/8`, ranges and budget; only the hypothesis `A ≥ 2` is
added, `docs/SOURCE-ISSUES.md#C38`; also `docs/SOURCE-ISSUES.md#C7`) to estimators that use an
independent random seed. Randomized estimators: a seed space `Ω` (in any universe, with any σ-algebra) with a probability measure `ν` and a map `π̂ : Ω → samples → stationary randomized policy`. The seed law does not depend on the model `i`, and the failure probability is taken under the product law `ν ⊗ P_i` of the seed and the samples. No measurability of `π̂` in the seed is assumed: for a non-measurable failure set the real measure is the outer probability (as in `Thm6_13_randomized`); when the set is measurable it is the probability. An inner-probability version is false in general. Every Markov-kernel estimator on the finite data space is of seeded form. The constant `1/8` is the printed one (`max ≥ 1/8`); the internal bound `P₀(E₀)+P₁(E₁) ≥ 1/4` loses nothing. The models `M₀, M₁, μ` and all constants are chosen before `(Ω, ν, π̂)`. The deterministic entry is the case `Ω = Unit`, `ν = δ_()`. Review: `docs/critic-rand73.md`. -/
def Thm7_3_corrected_randomized : Prop :=
    ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 8 →
    ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
      [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
      2 ≤ Fintype.card Action →
      0 < σ → σ ≤ 1 - c₀ → 1 / 2 ≤ γ → γ < 1 → 0 < ε → ε ≤ c₀ / (256 * (1 - γ)) →
      (N : ℝ) ≤ c₀ * Real.log 2 / (8192 * (1 - γ) ^ 2 * max (1 - γ) σ * ε ^ 2) →
      ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
        M₀.discount = γ ∧ M₁.discount = γ ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
          (est : Ω → ModelBasedPolicyLearning.Samples State Action N →
            StationaryPolicy State Action),
          1 / 8 ≤ max
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₀ N)).real
              {p | ε < robustOptimalValueAt tvBall M₀ σ μ -
                robustPolicyValueAt tvBall M₀ σ (est p.1 p.2) μ})
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₁ N)).real
              {p | ε < robustOptimalValueAt tvBall M₁ σ μ -
                robustPolicyValueAt tvBall M₁ σ (est p.1 p.2) μ})

open StatisticalRL StatisticalRL.RobustRL.Ch7 MeasureTheory in
/-- Corrected Theorem 7.3 for externally randomized estimators under the book's known-reward
convention, `thm:l1-lower-bound`, `chapters/robust_RL.tex:377–391` (known reward:
`generative_model_model_based.tex:31`; `robust_RL.tex:25`, `:206–215`). It extends
`Thm7_3_corrected_knownReward`: the two RMDPs share their reward (`M₀.reward = M₁.reward`), and the
hypotheses `S ≥ 2`, `A ≥ 2` are added (`docs/SOURCE-ISSUES.md#C38`; also `#C7`). Randomized estimators: a seed space `Ω` (in any universe, with any σ-algebra) with a probability measure `ν` and a map `π̂ : Ω → samples → stationary randomized policy`. The seed law does not depend on the model `i`, and the failure probability is taken under the product law `ν ⊗ P_i` of the seed and the samples. No measurability of `π̂` in the seed is assumed: for a non-measurable failure set the real measure is the outer probability (as in `Thm6_13_randomized`); when the set is measurable it is the probability. An inner-probability version is false in general. Every Markov-kernel estimator on the finite data space is of seeded form. The constant `1/8` is the printed one (`max ≥ 1/8`); the internal bound `P₀(E₀)+P₁(E₁) ≥ 1/4` loses nothing. The models `M₀, M₁, μ` and all constants are chosen before `(Ω, ν, π̂)`. The deterministic entry is the case `Ω = Unit`, `ν = δ_()`. Review: `docs/critic-rand73.md`. -/
def Thm7_3_corrected_knownReward_randomized : Prop :=
    ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 / 8 →
    ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
      [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
      2 ≤ Fintype.card State → 2 ≤ Fintype.card Action →
      0 < σ → σ ≤ 1 - c₀ → 1 / 2 ≤ γ → γ < 1 → 0 < ε → ε ≤ c₀ / (256 * (1 - γ)) →
      (N : ℝ) ≤ c₀ * Real.log 2 / (8192 * (1 - γ) ^ 2 * max (1 - γ) σ * ε ^ 2) →
      ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
        M₀.discount = γ ∧ M₁.discount = γ ∧ M₀.reward = M₁.reward ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
          (est : Ω → ModelBasedPolicyLearning.Samples State Action N →
            StationaryPolicy State Action),
          1 / 8 ≤ max
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₀ N)).real
              {p | ε < robustOptimalValueAt tvBall M₀ σ μ -
                robustPolicyValueAt tvBall M₀ σ (est p.1 p.2) μ})
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₁ N)).real
              {p | ε < robustOptimalValueAt tvBall M₁ σ μ -
                robustPolicyValueAt tvBall M₁ σ (est p.1 p.2) μ})

end Thm7_3

section Thm7_5

/-- Every finite carrier gets the discrete σ-algebra (as in the printed transcriptions of
`Formalization/RobustRL/Ch7/Ch7PrintedStatements.lean`); the generative sampling law is the
product of the nominal rows over all `((s,a), i)`. -/
local instance ch7StatementStateMeasurable75 (State : Type*) : MeasurableSpace State := ⊤

open StatisticalRL StatisticalRL.RobustRL.Ch7 in
/-- Corrected Theorem 7.5, `thm:chi2-lower-bound`, `chapters/robust_RL.tex:461–480` (χ²-robust
MDP `:19–157`, χ² divergence `intro.tex:228–234` with `q ≪ p`, generative sampling `:135–147`,
`:206–215`), corrected by adding the single hypothesis `A ≥ 2`
(`docs/SOURCE-ISSUES.md#C7`: the printed result is false at `A = 1`). There are universal
constants `c₃, c₄ > 0` such that for all `S` (the state type), `A ≥ 2`, `γ ∈ [3/4, 1)`,
`σ ∈ (0, ∞)`, `ε ≤ c₃/(1-γ)` and `N ≤ c₄/((1-γ)³ε²)·(1 + σ/(1-γ))`, there are two RMDPs
`M₀, M₁` on the given states and actions (discount `γ`, rewards in `[0,1]`,
`(s,a)`-rectangular χ² balls of radius `σ` around the nominal kernel) and an initial
distribution `μ` such that every estimator (a map from the `N` samples per state-action pair
to a stationary randomized policy) has `max_i P_i(V_i^{⋆,σ}(μ) - V_i^{π̂,σ}(μ) > ε) ≥ 1/8`.
No `ε > 0` is added: for `ε < 0` the claim is trivial; at `ε = 0` the Lean value `c₄/0 = 0`
forces `N = 0`, and the instance also holds for every `N` under the reading `c₄/0 = ∞`.
Here an estimator is a deterministic function of the samples; estimators with an independent random
seed are covered by `Thm7_5_corrected_randomized`, of which this entry is the `Ω = Unit` case.

Disclosure on the estimator class. `M₀` and `M₁` may have different rewards, and the
estimators see the samples only, not the reward.
* The `S = 1` case holds only because the estimators cannot see the reward (proof: a shared
  self-loop kernel with rewards `1[a = a_j]`). Under the book's known-reward convention
  (`generative_model_model_based.tex:31`; `robust_RL.tex:25`, `robust_RL.tex:206–215`) the
  printed claim is false at `S = 1` (machine-checked: `argmax r` is robust-optimal, C7).
* For `S ≥ 2` the proof uses two models with one shared reward that differ only in the
  nominal rows at `(s₀, a₀)` and `(s₀, a₁)`; the known-reward reading is
  `Thm7_5_corrected_knownReward`. -/
def Thm7_5_corrected : Prop :=
  ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧
  ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
    [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
    2 ≤ Fintype.card Action →
    3 / 4 ≤ γ → γ < 1 → 0 < σ → ε ≤ c₃ / (1 - γ) →
    (N : ℝ) ≤ c₄ / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ)) →
    ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
      M₀.discount = γ ∧ M₁.discount = γ ∧
      ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
        1 / 8 ≤ max
          ((ModelBasedPolicyLearning.samplingLaw M₀ N).real
            {data | ε < robustOptimalValueAt chiBall M₀ σ μ -
              robustPolicyValueAt chiBall M₀ σ (est data) μ})
          ((ModelBasedPolicyLearning.samplingLaw M₁ N).real
            {data | ε < robustOptimalValueAt chiBall M₁ σ μ -
              robustPolicyValueAt chiBall M₁ σ (est data) μ})

open StatisticalRL StatisticalRL.RobustRL.Ch7 in
/-- Corrected Theorem 7.5 under the book's known-reward convention: `thm:chi2-lower-bound`,
`chapters/robust_RL.tex:461–480`, read with the convention that the reward is known to the
learner (`generative_model_model_based.tex:31`; `robust_RL.tex:25`, `robust_RL.tex:206–215`),
encoded by requiring the two RMDPs to share their reward (`M₀.reward = M₁.reward`), so that
only the nominal kernel is unknown. This is the faithful reading of the printed result under
that convention. It is corrected by adding the hypotheses `S ≥ 2` and `A ≥ 2`
(`docs/SOURCE-ISSUES.md#C7`); both are needed there, and both necessities are machine-checked
(with one of them dropped the statement is false for every `c₃, c₄ > 0`). No `ε > 0` is added.
Every other constant, range and the conclusion are as printed (see `Thm7_5_corrected`). The
two models of the proof differ only in the nominal rows at `(s₀, a₀)` and `(s₀, a₁)`. Estimators
here are deterministic functions of the samples; seeded randomized estimators are covered by
`Thm7_5_corrected_knownReward_randomized`. -/
def Thm7_5_corrected_knownReward : Prop :=
  ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧
  ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
    [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
    2 ≤ Fintype.card State → 2 ≤ Fintype.card Action →
    3 / 4 ≤ γ → γ < 1 → 0 < σ → ε ≤ c₃ / (1 - γ) →
    (N : ℝ) ≤ c₄ / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ)) →
    ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
      M₀.discount = γ ∧ M₁.discount = γ ∧ M₀.reward = M₁.reward ∧
      ∀ est : ModelBasedPolicyLearning.Samples State Action N → StationaryPolicy State Action,
        1 / 8 ≤ max
          ((ModelBasedPolicyLearning.samplingLaw M₀ N).real
            {data | ε < robustOptimalValueAt chiBall M₀ σ μ -
              robustPolicyValueAt chiBall M₀ σ (est data) μ})
          ((ModelBasedPolicyLearning.samplingLaw M₁ N).real
            {data | ε < robustOptimalValueAt chiBall M₁ σ μ -
              robustPolicyValueAt chiBall M₁ σ (est data) μ})

open StatisticalRL StatisticalRL.RobustRL.Ch7 MeasureTheory in
/-- Corrected Theorem 7.5 for externally randomized estimators, `thm:chi2-lower-bound`,
`chapters/robust_RL.tex:461–480` (the printed infimum is over all estimators). It extends
`Thm7_5_corrected` (same universal constants `c₃, c₄ > 0`, ranges and budget; only the hypothesis
`A ≥ 2` is added, `docs/SOURCE-ISSUES.md#C7`; also `#C38`) to estimators that use an independent
random seed. Randomized estimators: a seed space `Ω` (in any universe, with any σ-algebra) with a probability measure `ν` and a map `π̂ : Ω → samples → stationary randomized policy`. The seed law does not depend on the model `i`, and the failure probability is taken under the product law `ν ⊗ P_i` of the seed and the samples. No measurability of `π̂` in the seed is assumed: for a non-measurable failure set the real measure is the outer probability (as in `Thm6_13_randomized`); when the set is measurable it is the probability. An inner-probability version is false in general. Every Markov-kernel estimator on the finite data space is of seeded form. The constant `1/8` is the printed one (`max ≥ 1/8`); the internal bound `P₀(E₀)+P₁(E₁) ≥ 1/4` loses nothing. The models `M₀, M₁, μ` and all constants are chosen before `(Ω, ν, π̂)`. The deterministic entry is the case `Ω = Unit`, `ν = δ_()`. Review: `docs/critic-rand73.md`. -/
def Thm7_5_corrected_randomized : Prop :=
    ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
      [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
      2 ≤ Fintype.card Action →
      3 / 4 ≤ γ → γ < 1 → 0 < σ → ε ≤ c₃ / (1 - γ) →
      (N : ℝ) ≤ c₄ / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ)) →
      ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
        M₀.discount = γ ∧ M₁.discount = γ ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
          (est : Ω → ModelBasedPolicyLearning.Samples State Action N →
            StationaryPolicy State Action),
          1 / 8 ≤ max
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₀ N)).real
              {p | ε < robustOptimalValueAt chiBall M₀ σ μ -
                robustPolicyValueAt chiBall M₀ σ (est p.1 p.2) μ})
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₁ N)).real
              {p | ε < robustOptimalValueAt chiBall M₁ σ μ -
                robustPolicyValueAt chiBall M₁ σ (est p.1 p.2) μ})

open StatisticalRL StatisticalRL.RobustRL.Ch7 MeasureTheory in
/-- Corrected Theorem 7.5 for externally randomized estimators under the book's known-reward
convention, `thm:chi2-lower-bound`, `chapters/robust_RL.tex:461–480` (known reward:
`generative_model_model_based.tex:31`; `robust_RL.tex:25`, `:206–215`). It extends
`Thm7_5_corrected_knownReward`: the two RMDPs share their reward, and the hypotheses `S ≥ 2`,
`A ≥ 2` are added (`docs/SOURCE-ISSUES.md#C7`; also `#C38`). Randomized estimators: a seed space `Ω` (in any universe, with any σ-algebra) with a probability measure `ν` and a map `π̂ : Ω → samples → stationary randomized policy`. The seed law does not depend on the model `i`, and the failure probability is taken under the product law `ν ⊗ P_i` of the seed and the samples. No measurability of `π̂` in the seed is assumed: for a non-measurable failure set the real measure is the outer probability (as in `Thm6_13_randomized`); when the set is measurable it is the probability. An inner-probability version is false in general. Every Markov-kernel estimator on the finite data space is of seeded form. The constant `1/8` is the printed one (`max ≥ 1/8`); the internal bound `P₀(E₀)+P₁(E₁) ≥ 1/4` loses nothing. The models `M₀, M₁, μ` and all constants are chosen before `(Ω, ν, π̂)`. The deterministic entry is the case `Ω = Unit`, `ν = δ_()`. Review: `docs/critic-rand73.md`. -/
def Thm7_5_corrected_knownReward_randomized : Prop :=
    ∃ c₃ c₄ : ℝ, 0 < c₃ ∧ 0 < c₄ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action] [Nonempty State]
      [Nonempty Action] (γ σ ε : ℝ) (N : ℕ),
      2 ≤ Fintype.card State → 2 ≤ Fintype.card Action →
      3 / 4 ≤ γ → γ < 1 → 0 < σ → ε ≤ c₃ / (1 - γ) →
      (N : ℝ) ≤ c₄ / ((1 - γ) ^ 3 * ε ^ 2) * (1 + σ / (1 - γ)) →
      ∃ (M₀ M₁ : DiscountedMDP State Action) (μ : FiniteDistribution State),
        M₀.discount = γ ∧ M₁.discount = γ ∧ M₀.reward = M₁.reward ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
          (est : Ω → ModelBasedPolicyLearning.Samples State Action N →
            StationaryPolicy State Action),
          1 / 8 ≤ max
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₀ N)).real
              {p | ε < robustOptimalValueAt chiBall M₀ σ μ -
                robustPolicyValueAt chiBall M₀ σ (est p.1 p.2) μ})
            ((ν.prod (ModelBasedPolicyLearning.samplingLaw M₁ N)).real
              {p | ε < robustOptimalValueAt chiBall M₁ σ μ -
                robustPolicyValueAt chiBall M₁ σ (est p.1 p.2) μ})

end Thm7_5

section Thm7_8

/-- Theorem 7.8 corrected (`thm:lower-marl`, `chapters/marl.tex:487–503`; `docs/SOURCE-ISSUES.md#C40`).

There are constants `c₁, c₂ > 0` such that for all `m ≥ 2`, `S ≥ 2`, `H ≥ 2` and action counts
`A_1, …, A_m` with `max_i A_i ≥ 2`, and every `0 < ε ≤ c₁ H`, there is a family `{MG_θ}` of
`m`-player zero-sum Markov games (`zeroSumAdm`: rewards sum to `0`, player 1's rewards in `[0,1]`,
all rewards in `[-1,1]`) with `S` states, horizon `H`, `A_i` actions, all sharing one reward table,
such that for every total sample size `N < c₂ H⁴ S max_i A_i / ε²` and every learner some `θ` has
`P_θ(gap(π̂) > ε) ≥ 1/4`. A learner is a discrete seed law `μ` on an arbitrary type `Ω`
(`μ ≥ 0`, `∑ μ = 1`), an adaptive randomized query rule (each generative-model call `(h, s, a)` is
drawn from a law depending on the seed and on all previous queries and answers), and an output joint
(possibly correlated) Markov policy computed from the seed and the full history of the `N` queries
and their answers.

Differences from the printed statement and disclosures:
* Size ranges `S ≥ 2`, `H ≥ 2`, `max_i A_i ≥ 2` are added. The printed statement is false for
  `A_i ≡ 1` (`not_thm7_8_printed`); for `S = 1` or `H = 1` a known game has an exact equilibrium.
  Minimality of `S, H, m ≥ 2` is argued in prose only (C40), not proved in Lean.
* The zero-sum convention for `m ≥ 3` is our choice (the source defines only `m = 2`); the hard
  family has only two non-dummy players. `Thm7_8_corrected_constSum` covers the normalised
  constant-sum reading. The reward predicates are imposed at every step `h : ℕ`, not only `h ≤ H`.
* Known reward is encoded by the shared reward table: the learner is quantified after the family.
* Randomization is discrete (countably supported seed law over any type): measurable output kernels
  into the continuous policy space are not literally quantified over. A general randomized output is
  a mixture of deterministic outputs and the failure probability is linear in the mixture, so this
  is a modelling choice rather than a mathematical loss.
* Outputs are joint Markov policies and best responses range over Markov player deviations
  `π'_i × π_{-i}`, as in the source.
* If some `A_j = 0` the query type is empty, no query rule exists, and the conclusion is vacuous;
  the source implicitly has `A_i ≥ 1`. -/
def Thm7_8_corrected : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
  ∀ (m S H : ℕ) (A : Fin m → ℕ), 2 ≤ m → 2 ≤ S → 2 ≤ H → 2 ≤ Finset.univ.sup A →
  ∀ ε : ℝ, 0 < ε → ε ≤ c₁ * H →
  ∃ (Θ : Type) (G : Θ → StatisticalRL.Ch7Rest.Marl.MarkovGame m S H A),
    (∀ θ, StatisticalRL.Ch7Rest.Marl.zeroSumAdm (G θ)) ∧
    (∀ θ θ', (G θ).reward = (G θ').reward) ∧
    ∀ N : ℕ, (N : ℝ) < c₂ * (H : ℝ) ^ 4 * S * ((Finset.univ.sup A : ℕ) : ℝ) / ε ^ 2 →
    ∀ (Ω : Type) (μ : Ω → ℝ), (∀ ω, 0 ≤ μ ω) → HasSum μ 1 →
    ∀ (rule : Ω → (t : ℕ) → (Fin t → StatisticalRL.Ch7Rest.Marl.Query m S H A × Fin S) →
        FiniteDistribution (StatisticalRL.Ch7Rest.Marl.Query m S H A))
      (out : Ω → (Fin N → StatisticalRL.Ch7Rest.Marl.Query m S H A × Fin S) →
        StatisticalRL.Ch7Rest.Marl.JointPolicy m S A),
    ∃ θ, (1 : ℝ) / 4 ≤ ∑' ω, μ ω *
      ∑ hist, (StatisticalRL.AdaptiveKL.interactionLaw (rule ω)
          (StatisticalRL.Ch7Rest.Marl.genEnv (G θ)) N).prob hist *
        (if ε < StatisticalRL.Ch7Rest.Marl.gapJ (G θ) (out ω hist) then 1 else 0)

/-- Theorem 7.8 corrected, normalised constant-sum variant (`thm:lower-marl`,
`chapters/marl.tex:487–503`; `docs/SOURCE-ISSUES.md#C40`). Identical to `Thm7_8_corrected` except that the
games satisfy `constSumAdm` (rewards sum to `1` over the players, every reward in `[0,1]`, i.e. the
reward normalisation of `marl.tex:41–43` with the constant shift allowed by the footnote at :53)
instead of `zeroSumAdm`. -/
def Thm7_8_corrected_constSum : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
  ∀ (m S H : ℕ) (A : Fin m → ℕ), 2 ≤ m → 2 ≤ S → 2 ≤ H → 2 ≤ Finset.univ.sup A →
  ∀ ε : ℝ, 0 < ε → ε ≤ c₁ * H →
  ∃ (Θ : Type) (G : Θ → StatisticalRL.Ch7Rest.Marl.MarkovGame m S H A),
    (∀ θ, StatisticalRL.Ch7Rest.Marl.constSumAdm (G θ)) ∧
    (∀ θ θ', (G θ).reward = (G θ').reward) ∧
    ∀ N : ℕ, (N : ℝ) < c₂ * (H : ℝ) ^ 4 * S * ((Finset.univ.sup A : ℕ) : ℝ) / ε ^ 2 →
    ∀ (Ω : Type) (μ : Ω → ℝ), (∀ ω, 0 ≤ μ ω) → HasSum μ 1 →
    ∀ (rule : Ω → (t : ℕ) → (Fin t → StatisticalRL.Ch7Rest.Marl.Query m S H A × Fin S) →
        FiniteDistribution (StatisticalRL.Ch7Rest.Marl.Query m S H A))
      (out : Ω → (Fin N → StatisticalRL.Ch7Rest.Marl.Query m S H A × Fin S) →
        StatisticalRL.Ch7Rest.Marl.JointPolicy m S A),
    ∃ θ, (1 : ℝ) / 4 ≤ ∑' ω, μ ω *
      ∑ hist, (StatisticalRL.AdaptiveKL.interactionLaw (rule ω)
          (StatisticalRL.Ch7Rest.Marl.genEnv (G θ)) N).prob hist *
        (if ε < StatisticalRL.Ch7Rest.Marl.gapJ (G θ) (out ω hist) then 1 else 0)

end Thm7_8

section Thm7_9

open StatisticalRL.Ch7Rest in
/-- Theorem 7.9 corrected (`thm:dist-syncq-local`, `chapters/federated_RL.tex:99–117`; FedSynQ,
algorithm :35–90, setup and sampling :19–29; `docs/SOURCE-ISSUES.md#C41`).

There are universal constants `c_T, c_η > 0` such that for every finite MDP (`S = |State|`,
`A = |Action|`, rewards in `[0,1]`, `0 < γ < 1`), every `K ≥ 1` agents, period `τ ≥ 1`, horizon
`T ≥ 1` with `τ ∣ T`, every `δ ∈ (0,1)`, `ε ∈ (0, 1/(1-γ)]` and initialization
`0 ≤ Q₀ ≤ 1/(1-γ)`: if `η = c_η K(1-γ)⁴ε² / log(SAKT/δ)` (114), `η < 1`,
`τ ≤ 1 + η⁻¹ min{(1-γ)/(8γ), 1/K}` (106) and
`T ≥ c_T/(K(1-γ)⁵ε²) · log³(SAKT/(δε(1-γ)²))` (112–113), then with probability at least `1-δ`
the FedSynQ output `Q_T = (1/K) Σ_k Q_T^k` (:68) satisfies `|Q_T(s,a) - Q⋆(s,a)| ≤ ε` for all
`(s,a)`. Here `Q_t^k` is `Fed.fedRun` (local update (47–49), averaging when `t ≡ 0 mod τ`
(59–64), `Q_0^k = Q₀`), the draws `s_t^k(s,a)` are read from the data by
`FedGeneric.fedSamplesExtend … 0`, and `log` is the natural logarithm.

Differences from the printed statement. It differs from the printed statement in hypotheses only
by the added hypothesis `η < 1`, i.e. `c_η K (1-γ)⁴ ε² < log(SAKT/δ)`: the printed `η` (114) is
never constrained to the algorithm's input range `0 < η < 1` (:51, :76), and under the literal
reading the printed statement is false (`Fed.Thm7_9_printed`, refuted by
`not_thm7_9_printed` in `Formalization/Ch7Rest/LargeStep79.lean`; C41). Beyond that hypothesis
the entry fixes or strengthens:
* the probability is under the true independent generative law
  `FedGeneric.fedSamplingLaw M T K 1` (:23–26), and `Q⋆` is the true optimal Q-function
  `M.optimalityFixedPoint` (the printed-reading Prop `Fed.Thm7_9_at` chooses both existentially);
* the constants `c_T, c_η` are universal and quantified before every other quantity (the source
  names them after `δ, ε, Q₀, τ`); the proof gives `c_η = 1/216`, `c_T = 10⁴`. The entry is
  existential in `(c_T, c_η)`: the alternative reading "for every sufficiently small `c_η`, with
  `c_T` fixed (and every sufficiently large `c_T`)" is not claimed here;
* `γ > 0` is kept as the definedness convention for the τ condition (106), which divides by `γ`:
  without it Lean's `1/0 = 0` would collapse (106) to `τ ≤ 1 + η⁻¹ min{0, 1/K}`, which is not the
  printed condition;
* `K, τ, T ≥ 1` are implicit in the source (:21, :56, :74). `τ ∣ T` is not a hypothesis of the
  printed theorem but the source's stated standing convention (:70, "Without loss of generality,
  we assume that `T` is divisible by the synchronization period `τ`"), so it is kept; the library
  export does not use it. -/
def Thm7_9_corrected : Prop :=
  ∃ c_T c_η : ℝ, 0 < c_T ∧ 0 < c_η ∧
  ∀ (State Action : Type) [Fintype State] [Fintype Action] (M : DiscountedMDP State Action)
    (K τ T : ℕ) (δ ε : ℝ) (Q₀ : State → Action → ℝ),
    1 ≤ K → 1 ≤ τ → 1 ≤ T → τ ∣ T → 0 < M.discount →
    0 < δ → δ < 1 → 0 < ε → ε ≤ 1 / (1 - M.discount) →
    (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - M.discount)) →
    ∀ η : ℝ,
    η = c_η * K * (1 - M.discount) ^ 4 * ε ^ 2 /
      Real.log (Fintype.card State * Fintype.card Action * K * T / δ) →
    η < 1 →
    (τ : ℝ) ≤ 1 + 1 / η * min ((1 - M.discount) / (8 * M.discount)) (1 / (K : ℝ)) →
    c_T / (K * (1 - M.discount) ^ 5 * ε ^ 2) *
        Real.log (Fintype.card State * Fintype.card Action * K * T /
          (δ * ε * (1 - M.discount) ^ 2)) ^ 3 ≤ T →
    1 - δ ≤ (FedGeneric.fedSamplingLaw M T K 1).real {data | ∀ s a,
      |Fed.fedOutput M η K τ Q₀
          (fun t k s a ↦ FedGeneric.fedSamplesExtend M T K 1 data t k s a 0) T s a -
        M.optimalityFixedPoint s a| ≤ ε}

open StatisticalRL.Ch7Rest in
/-- Per-agent sample size, restricted to the `K`-range where the prescribed step size is at most 1
(`eq:sample-size-per-agent-fedQ`, `chapters/federated_RL.tex:118–129`; `docs/SOURCE-ISSUES.md#C41`).

Printed claim (:120–127): Theorem 7.9 implies that each agent requires at most
`Õ(SA/(K(1-γ)⁵ε²))` samples for an `ε`-accurate estimate of `Q⋆`, each agent drawing `SA`
samples per iteration.

Entry: there are constants `C, c_η > 0` such that for every finite MDP (`0 ≤ γ < 1`), `K ≥ 1`,
`δ ∈ (0,1)`, `ε ∈ (0, 1/(1-γ)]` and `0 ≤ Q₀ ≤ 1/(1-γ)` with `c_η K(1-γ)⁴ε² ≤ log(SAK/δ)` (the
step size (114) at `T = 1` is at most 1), there is a horizon `T ≥ 1` with per-agent sample count
`SA·T ≤ C·SA/(K(1-γ)⁵ε²)·(1 + log(SAK/(δε(1-γ)²)))³` such that FedSynQ (Algorithm
`alg:dist-syncq-local`, :35–90) run for `T` iterations with the printed step size
`η = c_η K(1-γ)⁴ε²/log(SAKT/δ)` (114) and any period `τ ≥ 1` obeying (106) outputs
`Q_T = (1/K)Σ_k Q_T^k` with `|Q_T(s,a) - Q⋆(s,a)| ≤ ε` for all `(s,a)` with probability at least
`1-δ` under the true generative law `FedGeneric.fedSamplingLaw M T K 1`; `Q⋆` is
`M.optimalityFixedPoint`. The proof gives `C = 270000216`, `c_η = 1/216`.

Differences from the printed claim. The `Õ` is made explicit as the cube of
`1 + log(SAK/(δε(1-γ)²))`. The claim is restricted to `c_η K(1-γ)⁴ε² ≤ log(SAK/δ)`, i.e.
`K ≲ log(SAK/δ)/((1-γ)⁴ε²)`: the corrected Theorem 7.9 needs `η ≤ 1` (C41), and for
`K ≫ log(SAK/δ)/((1-γ)⁴ε²)` the corrected theorem only certifies horizons
`T ≥ δ·exp(c_η K(1-γ)⁴ε²)/(SAK)`, exponential in `K` (library lemma
`FedSync.horizon_ge_exp_of_eta_le_one`), so the unrestricted read-off (linear speedup for every
`K`) is not implied by the theorem. It is not refuted either: whether FedSynQ attains it for larger
`K` is open. The entry has no `0 < γ` hypothesis (unlike `Thm7_9_corrected`): at `γ = 0` (outside
the theorem's `γ ∈ (0,1)`) Lean's `1/0 = 0` makes condition (106) force `τ = 1`, a narrower range
of `τ` than the printed reading; for `γ > 0` the condition is the printed (106). See
`docs/SOURCE-ISSUES.md` C41. -/
def Eq_sample_size_per_agent_fedQ_restricted : Prop :=
  ∃ C c_η : ℝ, 0 < C ∧ 0 < c_η ∧
  ∀ (State Action : Type) [Fintype State] [Fintype Action] (M : DiscountedMDP State Action)
    (K : ℕ) (δ ε : ℝ) (Q₀ : State → Action → ℝ),
    1 ≤ K → 0 < δ → δ < 1 → 0 < ε → ε ≤ 1 / (1 - M.discount) →
    (∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - M.discount)) →
    c_η * K * (1 - M.discount) ^ 4 * ε ^ 2 ≤
      Real.log (Fintype.card State * Fintype.card Action * K / δ) →
    ∃ T : ℕ, 1 ≤ T ∧
      (Fintype.card State * Fintype.card Action * T : ℝ) ≤
        C * (Fintype.card State * Fintype.card Action) / (K * (1 - M.discount) ^ 5 * ε ^ 2) *
          (1 + Real.log (Fintype.card State * Fintype.card Action * K /
            (δ * ε * (1 - M.discount) ^ 2))) ^ 3 ∧
      ∀ (τ : ℕ) (η : ℝ), 1 ≤ τ →
        η = c_η * K * (1 - M.discount) ^ 4 * ε ^ 2 /
          Real.log (Fintype.card State * Fintype.card Action * K * T / δ) →
        (τ : ℝ) ≤ 1 + 1 / η * min ((1 - M.discount) / (8 * M.discount)) (1 / (K : ℝ)) →
        1 - δ ≤ (FedGeneric.fedSamplingLaw M T K 1).real {data | ∀ s a,
          |Fed.fedOutput M η K τ Q₀
              (fun t k s a ↦ FedGeneric.fedSamplesExtend M T K 1 data t k s a 0) T s a -
            M.optimalityFixedPoint s a| ≤ ε}

end Thm7_9

section Thm7_2_7_4

/-- Discrete σ-algebra on every finite carrier, as in the printed transcriptions of
`Formalization/RobustRL/Ch7/Ch7PrintedStatements.lean`. -/
local instance ch7StatementStateMeasurable72 (State : Type*) : MeasurableSpace State := ⊤

open StatisticalRL StatisticalRL.RobustRL.Ch7 in
/-- Corrected Theorem 7.2, `thm:l1-upper-bound`, `chapters/robust_RL.tex:342–359` (TV-robust
MDP `:19–157`, DRVI = Algorithm `alg:cvi-dro-infinite` `:243–289`, generative sampling
`:135–147`, `:206–215`). It differs from the printed result only in the iteration count
(`docs/SOURCE-ISSUES.md#C37`): DRVI may run for any `T ∈ ℕ` with
`T ≥ C₁ log(N/(1−γ))/(1−γ)` instead of `T = C₁ log(N/(1−γ))` (`:345`). This is a minimal edit
of the printed formula: the factor `1/(1−γ)` is necessary (C37 horizon trap), but tightness of
the `log(N/(1−γ))` factor is not shown.

For universal constants `C₁, C₂ > 0` (proved with `C₁ = 2`, `C₂ = 10⁶`), every finite `S`, `A`,
every RMDP with discount `γ ∈ [1/4, 1)`, TV radius `σ ∈ (0,1)`, `δ ∈ (0,1)`,
`ε ∈ (0, √(1/max{1−γ,σ})]`, `N > 0` with
`N ≥ C₂ log(SAN/((1−γ)δ)) / ((1−γ)² max{1−γ,σ} ε²)`, every such `T` and every greedy selector
`π̂` of `Q̂_T` (ties unspecified, `:254–258`): with probability at least `1−δ` over the samples,
`V^{⋆,σ}(s) − V^{π̂,σ}(s) ≤ ε` for all `s`. Robust values are infima of actual trajectory
values over `(s,a)`-rectangular kernels; `V^{⋆,σ}` is the supremum over stationary randomized
policies. Not covered: the oracle-planner Remark (`:361–372`) and history-dependent policies. -/
def Thm7_2_corrected : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (σ δ ε : ℝ) (N : ℕ) (hN : 0 < N),
      1 / 4 ≤ M.discount → 0 < σ → σ < 1 → 0 < δ → δ < 1 → 0 < ε →
      ε ≤ Real.sqrt (1 / max (1 - M.discount) σ) →
      C₂ / ((1 - M.discount) ^ 2 * max (1 - M.discount) σ * ε ^ 2) *
          Real.log (Fintype.card State * Fintype.card Action * N /
            ((1 - M.discount) * δ)) ≤ N →
      ∀ T : ℕ, C₁ * Real.log (N / (1 - M.discount)) / (1 - M.discount) ≤ T →
      ∀ pick : ModelBasedPolicyLearning.Samples State Action N → State → Action,
        (∀ data, IsGreedy (empiricalDRVI tvBall M σ N hN data T) (pick data)) →
        1 - δ ≤ (ModelBasedPolicyLearning.samplingLaw M N).real
          {data | ∀ s, robustOptimalValue tvBall M σ s -
            robustPolicyValue tvBall M σ (detPolicy (pick data)) s ≤ ε}

open StatisticalRL StatisticalRL.RobustRL.Ch7 in
/-- Corrected Theorem 7.4, `thm:l2-upper-bound`, `chapters/robust_RL.tex:437–450` (χ²-robust
MDP with the support-aware χ² ball, `intro.tex:228–234`). It differs from the printed result only
in the iteration count (`docs/SOURCE-ISSUES.md#C37`): any `T ∈ ℕ` with
`T ≥ c₁ log(N/(1−γ))/(1−γ)` instead of `T = c₁ log(N/(1−γ))` (`chapters/robust_RL.tex:438`). This is a minimal edit
of the printed formula; tightness of the log factor is not shown.

For universal constants `c₁, c₂ > 0` (proved with `c₁ = 2`, `c₂ = 10⁶`), every finite `S`, `A`,
every RMDP with `σ > 0`, `γ ∈ [1/4, 1)`, `δ ∈ (0,1)`, `ε ∈ (0, 1/(1−γ)]`, `N > 0` with
`N ≥ c₂ (1 + max{√σ,σ}/(1−γ)) log(SAN/δ) / ((1−γ)³ ε²)`, every such `T` and every greedy
selector `π̂` of `Q̂_T`: with probability at least `1−δ`, `V^{⋆,σ}(s) − V^{π̂,σ}(s) ≤ ε` for all
`s`. The oracle-planner Remark (`chapters/robust_RL.tex:453–457`) is indexed separately as `Remark7_2_restricted`. Not
covered: history-dependent policies. -/
def Thm7_4_corrected : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (σ δ ε : ℝ) (N : ℕ) (hN : 0 < N),
      0 < σ → 1 / 4 ≤ M.discount → 0 < δ → δ < 1 → 0 < ε →
      ε ≤ 1 / (1 - M.discount) →
      c₂ / ((1 - M.discount) ^ 3 * ε ^ 2) *
          (1 + max (Real.sqrt σ) σ / (1 - M.discount)) *
          Real.log (Fintype.card State * Fintype.card Action * N / δ) ≤ N →
      ∀ T : ℕ, c₁ * Real.log (N / (1 - M.discount)) / (1 - M.discount) ≤ T →
      ∀ pick : ModelBasedPolicyLearning.Samples State Action N → State → Action,
        (∀ data, IsGreedy (empiricalDRVI chiBall M σ N hN data T) (pick data)) →
        1 - δ ≤ (ModelBasedPolicyLearning.samplingLaw M N).real
          {data | ∀ s, robustOptimalValue chiBall M σ s -
            robustPolicyValue chiBall M σ (detPolicy (pick data)) s ≤ ε}

open StatisticalRL StatisticalRL.RobustRL.Ch7 in
/-- Restricted Remark 7.1, `remark:tv-upper`, `chapters/robust_RL.tex:361–372` (with
`eq:oracle_requirement`, :365–369), for Theorem 7.2 `thm:l1-upper-bound` (:342–359): the guarantee
of Theorem 7.2 holds for any planner run on the empirical RMDP (nominal kernel `P̂⁰`, TV ball of
radius `σ`) whose output `π̂` obeys `‖V̂^{⋆,σ} − V̂^{π̂,σ}‖∞ ≤ Õ((1−γ)²/N)`.

Reading: the `Õ` is `c_opt (1−γ)² log(SAN/((1−γ)δ)) / N` for an arbitrary constant `c_opt ≥ 0` (the
logarithmic factor is the one commented out at :367); the universal `C₂` may depend on `c_opt` (`∀
c_opt ∃ C₂`). Two supporting claims are paper arguments (plan check §3), not formalized: the reverse
order is false, since a huge `c_opt` admits arbitrarily bad planners; and higher powers of the
logarithm cannot be admitted, since the remark would then fail as `δ → 0`. The ℓ∞ requirement is
written coordinatewise with `|·|`; since `V̂^{⋆,σ} ≥ V̂^{π̂,σ}` always, it is equivalent to the
one-sided form. The DRVI iteration count (`docs/SOURCE-ISSUES.md#C37`) does not enter. Premises on
`γ, σ, δ, ε, N` are those of `Thm7_2_corrected` (with `N > 0`). `V̂^{⋆,σ}`, `V̂^{π̂,σ}` are the
robust values of the empirical model `ModelBasedPolicyLearning.empiricalModel M N hN data`;
`V^{⋆,σ}` is the supremum over stationary randomized policies, as in `Thm7_2_corrected`.

Restriction (`docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`): planner outputs are
deterministic stationary policies `detPolicy f`; randomized and history-dependent outputs are not
covered. The event does not depend on the planner: with probability at least `1−δ`, every `f`
meeting the requirement on the realized data set is `ε`-optimal, so any data-dependent planner is
covered without a measurability assumption. -/
def Remark7_1_restricted : Prop :=
  ∀ c_opt : ℝ, 0 ≤ c_opt → ∃ C₂ : ℝ, 0 < C₂ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (σ δ ε : ℝ) (N : ℕ) (hN : 0 < N),
      1 / 4 ≤ M.discount → 0 < σ → σ < 1 → 0 < δ → δ < 1 → 0 < ε →
      ε ≤ Real.sqrt (1 / max (1 - M.discount) σ) →
      C₂ / ((1 - M.discount) ^ 2 * max (1 - M.discount) σ * ε ^ 2) *
          Real.log (Fintype.card State * Fintype.card Action * N /
            ((1 - M.discount) * δ)) ≤ N →
      1 - δ ≤ (ModelBasedPolicyLearning.samplingLaw M N).real
        {data | ∀ f : State → Action,
          (∀ s, |robustOptimalValue tvBall
                (ModelBasedPolicyLearning.empiricalModel M N hN data) σ s -
              robustPolicyValue tvBall
                (ModelBasedPolicyLearning.empiricalModel M N hN data) σ (detPolicy f) s| ≤
            c_opt * (1 - M.discount) ^ 2 / N *
              Real.log (Fintype.card State * Fintype.card Action * N /
                ((1 - M.discount) * δ))) →
          ∀ s, robustOptimalValue tvBall M σ s -
            robustPolicyValue tvBall M σ (detPolicy f) s ≤ ε}

open StatisticalRL StatisticalRL.RobustRL.Ch7 in
/-- Restricted Remark 7.2, `remark:chi2-upper`, `chapters/robust_RL.tex:453–457`, for Theorem 7.4
`thm:l2-upper-bound` (:437–450): the guarantee of Theorem 7.4 holds for any planner run on the
empirical RMDP (nominal kernel `P̂⁰`, χ² ball of radius `σ`) whose output `π̂` obeys
`‖V̂^{⋆,σ} − V̂^{π̂,σ}‖∞ ≤ O(log(SAN/((1−γ)δ))/N²)`.

Reading: the `O(·)` is `c_opt · log(SAN/((1−γ)δ)) / N²` for an arbitrary constant `c_opt ≥ 0`, and
the universal `c₂` may depend on `c_opt` (`∀ c_opt ∃ c₂`, as in `Remark7_1_restricted`; proved with
`c₂ = 10⁶ + 8 c_opt`). The reverse order (`∃ c₂ ∀ c_opt`) is false for the same reason as in
Remark 7.1 (a huge `c_opt` admits arbitrarily bad planners); this is a paper argument, not
formalized. The ℓ∞ requirement is written coordinatewise with `|·|`; since `V̂^{⋆,σ} ≥ V̂^{π̂,σ}`
always, it is equivalent to the one-sided form. The DRVI iteration count
(`docs/SOURCE-ISSUES.md#C37`) does not enter. Premises on `σ, γ, δ, ε, N` are those of
`Thm7_4_corrected` (with `N > 0`), including its sample-size condition with `log(SAN/δ)`.
`V̂^{⋆,σ}`, `V̂^{π̂,σ}` are the robust values of the empirical model
`ModelBasedPolicyLearning.empiricalModel M N hN data`; `V^{⋆,σ}` is the supremum over stationary
randomized policies, as in `Thm7_4_corrected`.

Restriction (`docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`): planner outputs are
deterministic stationary policies `detPolicy f`; randomized and history-dependent outputs are not
covered. The event does not depend on the planner: with probability at least `1−δ`, every `f`
meeting the requirement on the realized data set is `ε`-optimal, so any data-dependent planner is
covered without a measurability assumption. -/
def Remark7_2_restricted : Prop :=
  ∀ c_opt : ℝ, 0 ≤ c_opt → ∃ c₂ : ℝ, 0 < c₂ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action]
      (M : DiscountedMDP State Action) (σ δ ε : ℝ) (N : ℕ) (hN : 0 < N),
      0 < σ → 1 / 4 ≤ M.discount → 0 < δ → δ < 1 → 0 < ε →
      ε ≤ 1 / (1 - M.discount) →
      c₂ / ((1 - M.discount) ^ 3 * ε ^ 2) *
          (1 + max (Real.sqrt σ) σ / (1 - M.discount)) *
          Real.log (Fintype.card State * Fintype.card Action * N / δ) ≤ N →
      1 - δ ≤ (ModelBasedPolicyLearning.samplingLaw M N).real
        {data | ∀ f : State → Action,
          (∀ s, |robustOptimalValue chiBall
                (ModelBasedPolicyLearning.empiricalModel M N hN data) σ s -
              robustPolicyValue chiBall
                (ModelBasedPolicyLearning.empiricalModel M N hN data) σ (detPolicy f) s| ≤
            c_opt / (N : ℝ) ^ 2 *
              Real.log (Fintype.card State * Fintype.card Action * N /
                ((1 - M.discount) * δ))) →
          ∀ s, robustOptimalValue chiBall M σ s -
            robustPolicyValue chiBall M σ (detPolicy f) s ≤ ε}

end Thm7_2_7_4

section Thm7_11

open StatisticalRL StatisticalRL.Ch7Rest.TDInference in
/-- Theorem 7.11 (`thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`; convex distance
`eqn:convex-distance` :124–127; `Λ⋆` :104–117), corrected covariance, all convex sets, instance constant.
Differs from the printed result in two ways.
(1) `Γ` is the true per-sample TD-noise covariance `trueGamma`,
`Γ_ss = μ(s) E_{a∼π(·|s), s'∼P(·|s,a)}[(V^π(s) − r(s,a) − γV^π(s'))²]`, so the Gaussian is
`N(0, Λ)` with `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`, `A = diag(μ)(I − γP_π)`. The printed `Γ` (:115) averages only over
`s' ∼ P_π` with an undefined `r(s)`; read as `r_π(s)` it omits the action-reward variance and the cross term
`2γCov(r(s,a), V^π(s'))`, and the printed theorem is then false (SOURCE-ISSUES C43). With state-only rewards
(or deterministic `π`) the two coincide.
(2) The `T^{-1/3}` constant `K` depends on the instance, `η₀` and `V₀`. It is not shown to be a universal multiple of
the printed `√(η₀/((1−γ)λ₀))Tr Γ‖Γ⁻¹‖ + √(Sκ(Γ))/((1−γ)λ₀η₀)`, and `C̃T^{-1/2}` is absorbed into `K`, so it is not
shown polynomial.
Kept: the printed rate `T^{-1/3}`; `d_cvx` over all convex `C ⊆ ℝ^S` (written as a bound for every convex `C`;
non-measurable `C` allowed, the Gaussian side being the outer measure); `η_t = η₀t^{-2/3}` with `0 < η₀ < 1/4` (:133);
i.i.d. sampling with full-support `μ` (:51–67); the asynchronous TD update (:72); the Polyak–Ruppert average (:82);
every `V₀`; `d = S`. `Γ_true ≻ 0` is assumed, the corrected analogue of the printed `‖Γ⁻¹‖`, `κ(Γ)` being finite.
`lawProb` is the exact i.i.d. law of `√TΔ̄_T`; `gaussCov (tdA M π μ) (trueGamma M π μ)` is `N(0, Λ)`.
Our own proof (randomized concentration for polyhedral representations of convex sets plus leave-one-out TD
estimates), not the cited paper's. Implies `Thm7_11_corrected_halfspace`.
Not implied: the printed coefficient; the printed statement under the state-only-reward reading; any confidence
region with the estimated covariance `Λ̂_T` (SOURCE-ISSUES C47). -/
def Thm7_11_corrected : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K : ℝ, 0 < K ∧
    ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C →
      |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
        K * (T : ℝ) ^ (-(1 / 3 : ℝ))

open StatisticalRL StatisticalRL.Ch7Rest.TDInference in
/-- Theorem 7.11 (`thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`), corrected covariance, closed
half-spaces only, instance constant. Differs from the printed result in three ways.
(1) `Γ` is the true per-sample TD-noise covariance `trueGamma`,
`Γ_ss = μ(s) E_{a∼π(·|s), s'∼P(·|s,a)}[(V^π(s) − r(s,a) − γV^π(s'))²]`. The printed `Γ` (:115) averages only over
`s' ∼ P_π` with an undefined `r(s)`; read as `r_π(s)`, it omits the action-reward variance and the cross term
`2γCov(r(s,a), V^π(s'))`, and the printed theorem is then false (SOURCE-ISSUES C43). With state-only rewards
(`r(s,a) = r(s)`) the two coincide.
(2) The sets are closed half-spaces `{x | ∑ s, u s * x s ≤ b}` (uniformly in `u`, `b`), not all convex sets in
`ℝ^S`.
(3) The `T^{-1/3}` constant `K` depends on the instance, `η₀` and `V₀`. It is not shown to be a universal multiple of
the printed `√(η₀/((1−γ)λ₀))Tr Γ‖Γ⁻¹‖ + √(Sκ(Γ))/((1−γ)λ₀η₀)`, and `C̃T^{-1/2}` is absorbed into `K`, so it is not
shown polynomial.
Kept: the printed rate `T^{-1/3}`; `η_t = η₀t^{-2/3}` with `0 < η₀ < 1/4` (:133); i.i.d. sampling with
full-support `μ` (:51–67); the asynchronous TD update (:72); the Polyak–Ruppert average (:82); every `V₀`; `d = S`.
`Γ_true ≻ 0` is assumed, since the printed coefficient uses `‖Γ⁻¹‖` and `κ(Γ)`. `lawProb` is the exact i.i.d. law of
`√TΔ̄_T`. `gaussCov (tdA M π μ) (trueGamma M π μ)` is `N(0, A⁻¹ΓA⁻ᵀ)` with `A = diag(μ)(I − γP_π)` (:106–117).
Implied by `Thm7_11_corrected` (half-spaces are convex), which covers all convex sets; kept as a supporting
entry with its own proof route (Chen–Shao nonlinear Stein bound on one-dimensional projections).
Not implied:
* the printed coefficient, which remains open;
* any confidence region with the estimated covariance `Λ̂_T` (SOURCE-ISSUES C47(1)–(4)), or beyond the
  oracle-covariance half-lines, slabs and Bonferroni box of `Eq_convex_Cdelta_corrected_oracle`, which are
  its corollaries. -/
def Thm7_11_corrected_halfspace : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K : ℝ, 0 < K ∧
    ∀ T : ℕ, 1 ≤ T → ∀ (u : State → ℝ) (b : ℝ),
      |lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤ b} -
        (gaussCov (tdA M π μ) (trueGamma M π μ)).real {x | ∑ s, u s * x s ≤ b}| ≤
        K * (T : ℝ) ^ (-(1 / 3 : ℝ))

end Thm7_11

section EqClassicClt

open StatisticalRL StatisticalRL.Ch7Rest.TDInference in
/-- Display `eqn:classic-clt` (`chapters/inference.tex:100–103`, prose :98; `Λ⋆ = A⁻¹ΓA⁻ᵀ`, `A`, `Γ`
:104–117), corrected covariance. `√T Δ̄_T →d N(0, A⁻¹ Γ_true A⁻ᵀ)`: for every bounded continuous
`g : (State → ℝ) → ℝ` (sup norm on `ℝ^S`), `E g(√T Δ̄_T) → ∫ g dN(0, A⁻¹ diag(Γ_true) A⁻ᵀ)` as
`T → ∞`, which is the definition of convergence in distribution.
Differs from the printed display in one way: `Γ` is the true per-sample TD-noise covariance
`trueGamma`, `Γ_ss = μ(s) E_{a∼π(·|s), s'∼P(·|s,a)}[(V^π(s) − r(s,a) − γV^π(s'))²]`. With the
printed `Γ` (`r(s)` read as `r_π(s)`) the display is false under action-dependent rewards
(SOURCE-ISSUES C43; Lean refutation
`StatisticalRL.Ch7Rest.TDInference.not_eq_classic_clt_printed` and
`StatisticalRL.Ch7Rest.TDInference.not_eq_classic_clt_printed_someInit`, which refute the
display for the printed step-size family `η_t = η₀t^{-2/3}` (`η₀ ∈ (0,1/4)` for every `V₀`;
`η₀ ∈ (0,1]` and some `V₀` for `_someInit`). The display is existential in the schedule; for
`V₀ = V^π` the same zero-noise argument refutes it for every schedule (paper argument, not
Lean-checked, since `tdIter` fixes the schedule). The reading "some schedule and some `V₀`" over
arbitrary schedules is not refuted).
Schedule: the display says "with an appropriate choice of the learning rate schedule" (:98), an
existential; this entry fixes the printed Theorem 7.11 schedule `η_t = η₀t^{-2/3}` with
`0 < η₀ < 1/4` (:133) and proves the convergence for every such `η₀` and every `V₀`, which
implies the existential. Kept: i.i.d. sampling with full-support `μ` (:51–67), the asynchronous
TD update (:72), the Polyak–Ruppert average (:82), `Δ̄_T` (:86–88), everything else fixed as
`T → ∞`. No `Γ_true ≻ 0` hypothesis: the limit may be degenerate. The statement is qualitative
(no rate) and makes no confidence-region claim. -/
def Eq_classic_clt_corrected : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 →
    ∀ g : BoundedContinuousFunction (State → ℝ) ℝ,
      Filter.Tendsto
        (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action,
          pathWeight M π μ ω * g (scaledError M π η₀ V₀ ω))
        Filter.atTop
        (nhds (∫ x, g x ∂(gaussCov (tdA M π μ) (trueGamma M π μ))))

open StatisticalRL StatisticalRL.Ch7Rest.TDInference in
/-- Display `eqn:classic-clt` (`chapters/inference.tex:100–103`, prose :98; `Λ⋆`, `A`, `Γ` :104–117)
with the printed `Γ`, restricted to instances where the reward `r(s,·)` is constant on the
support of `π(·|s)` for every state `s` (this covers state-only rewards `r(s,a) = r(s)` and
deterministic policies). On this class the printed `r(s)` is unambiguous (`= r_π(s)`) and the
printed `Γ` equals the true TD-noise covariance, so the printed display holds. Differs from the
printed display only by this restriction of the MDP class: outside it, under action-dependent
rewards with `r(s) := r_π(s)`, the display is false (SOURCE-ISSUES C43; Lean refutations
`StatisticalRL.Ch7Rest.TDInference.not_eq_classic_clt_printed` and
`StatisticalRL.Ch7Rest.TDInference.not_eq_classic_clt_printed_someInit`, for the printed
step-size family only; see `Eq_classic_clt_corrected` for their schedule scope).
Schedule `η_t = η₀t^{-2/3}`, `0 < η₀ < 1/4` (:133), every `V₀`; the printed "appropriate
schedule" is existential, so this family suffices. Convergence in distribution is stated as
convergence of `E g(√T Δ̄_T)` for every bounded continuous `g`. -/
def Eq_classic_clt_restricted : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s a a', 0 < (π s).prob a → 0 < (π s).prob a' → M.reward s a = M.reward s a') →
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 →
    ∀ g : BoundedContinuousFunction (State → ℝ) ℝ,
      Filter.Tendsto
        (fun T : ℕ ↦ ∑ ω : Fin T → Tuple State Action,
          pathWeight M π μ ω * g (scaledError M π η₀ V₀ ω))
        Filter.atTop
        (nhds (∫ x, g x ∂(gaussCov (tdA M π μ) (printedGamma M π μ))))

end EqClassicClt

section EqConvexCdelta

open StatisticalRL StatisticalRL.Ch7Rest.TDInference MeasureTheory ProbabilityTheory Matrix in
/-- Corrected (fixed-shape) and oracle-restricted variant of the confidence-set rule `eq:convex.Cdelta`
(`chapters/inference.tex:189–195`, display :191–193) and of the claim that "such sets serve as approximate
confidence regions" (:196); rectangle prose :198–205. See `docs/SOURCE-ISSUES.md#C47` and `#C43`.

Differs from the printed text: (1) the printed claim for arbitrary convex sets chosen from the data is false
(C47(1); Lean evidence for the oracle variant in `TDInferenceC47Evidence711.lean`); here the direction `u` and level
`z` are fixed before the data, the C47 proposed correction. (2) The covariance is the oracle
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`, the population target of the printed plug-in `Λ̂_T` (:180–182), unknown in practice;
`Γ_true` is the true residual covariance, not the printed `Γ` of `Λ*` (:115, C43). The plug-in rule is the separate
entry `Eq_convex_Cdelta_corrected_plugin` (with the finite-`T` rate `T^{-1/3}`).
(3) Only half-lines, slabs and a Bonferroni box; corrected forms of the `ℓ∞` rectangle (C47(2)) and the ellipsoid
(C47(3)) are the separate entries `Eq_convex_Cdelta_rectangle_corrected_oracle` and
`Eq_convex_Cdelta_ellipsoid_corrected_oracle` (rate `T^{-1/3}`). `Γ_true ≻ 0` is assumed. Kept: i.i.d. sampling, full-support `μ`,
`0 < η₀ < 1/4` (:133), every `V₀`, the rate `T^{-1/3}` with an instance constant `K`.

Statement: there is one `K > 0` such that for all `T ≥ 1`, with `Φ(z) = N(0,1)(−∞, z]` and `S = |State|`:
(1) all `z ∈ ℝ`, `u ≠ 0`: `|P(uᵀV̄_T − z√(uᵀΛu/T) ≤ uᵀV^π) − Φ(z)| ≤ K T^{-1/3}`;
(2) `z ≥ 0`, `u ≠ 0`: `|P(|uᵀ(V̄_T − V^π)| ≤ z√(uᵀΛu/T)) − (2Φ(z) − 1)| ≤ 2K T^{-1/3}`;
(3) `z ≥ 0`: `P(∀ s, |V̄_T(s) − V^π(s)| ≤ z√(Λ_ss/T)) ≥ 1 − 2S(1 − Φ(z)) − 2SK T^{-1/3}`. -/
def Eq_convex_Cdelta_corrected_oracle : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T →
      (∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ,
        |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∑ s, u s * prAverage M η₀ V₀ ω' s -
              z * Real.sqrt ((∑ s, ∑ s', u s * u s' *
                ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s') / T) ≤
              ∑ s, u s * M.valueFixedPoint π s}.indicator 1 ω) -
          (gaussianReal 0 1).real (Set.Iic z)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ, 0 ≤ z →
        |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action |
              |∑ s, u s * (prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s)| ≤
                z * Real.sqrt ((∑ s, ∑ s', u s * u s' *
                  ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ) s s') /
                    T)}.indicator 1 ω) -
          (2 * (gaussianReal 0 1).real (Set.Iic z) - 1)| ≤
            2 * K * (T : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (∀ z : ℝ, 0 ≤ z →
        1 - 2 * (Fintype.card State : ℝ) * (1 - (gaussianReal 0 1).real (Set.Iic z)) -
            2 * (Fintype.card State : ℝ) * K * (T : ℝ) ^ (-(1 / 3 : ℝ)) ≤
          ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∀ s,
              |prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s| ≤
                z * Real.sqrt ((((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) *
                  (tdA M π μ)⁻¹ᵀ) s s) / T)}.indicator 1 ω)

open StatisticalRL StatisticalRL.Ch7Rest.TDInference MeasureTheory ProbabilityTheory Matrix in
/-- Corrected (fixed-shape) plug-in rule `eq:convex.Cdelta` (`chapters/inference.tex:187–196`,
display :191–193, claim :196; plug-in `Λ̂_T` `eq:defn-hat-Lambda` :180–182; rectangles :198–205),
finite-`T` rate. See `docs/SOURCE-ISSUES.md#C47` and `#C43`.

Differs from the printed text: (1) direction `u` and level `z` fixed before the data (C47(1); the
printed claim for data-selected convex sets is false). (2) One instance constant `K > 0` (depends on
`M, π, μ, η₀, V₀`; not on `T`, `u`, `z`), rate `T^{-1/3}` as in Theorem 7.11; no printed coefficient.
(3) Added `Γ_true ≻ 0`; target `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (C43), not the printed `Λ⋆`. (4) Junk value
`Λ̂_T = 0` on the singular event (C47(4)); that event lies in the charged bad event, so the bound does
not depend on the convention. This rate statement implies the earlier asymptotic limits.
Kept: i.i.d. sampling, full-support `μ`, `0 < η₀ < 1/4` (:133), every `V₀`. -/
def Eq_convex_Cdelta_corrected_plugin : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T →
      (∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ,
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∑ s, u s * prAverage M η₀ V₀ ω' s -
              z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω' s s') / T) ≤
              ∑ s, u s * M.valueFixedPoint π s}.indicator 1 ω -
          (gaussianReal 0 1).real (Set.Iic z)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (∀ u : State → ℝ, u ≠ 0 → ∀ z : ℝ, 0 ≤ z →
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action |
              |∑ s, u s * (prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s)| ≤
                z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω' s s') /
                  T)}.indicator 1 ω -
          (2 * (gaussianReal 0 1).real (Set.Iic z) - 1)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (∀ z : ℝ, 0 ≤ z →
        1 - 2 * (Fintype.card State : ℝ) * (1 - (gaussianReal 0 1).real (Set.Iic z)) -
            K * (T : ℝ) ^ (-(1 / 3 : ℝ)) ≤
          ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∀ s,
              |prAverage M η₀ V₀ ω' s - M.valueFixedPoint π s| ≤
                z * Real.sqrt (lambdaHat M η₀ V₀ ω' s s / T)}.indicator 1 ω)

open StatisticalRL StatisticalRL.Ch7Rest.TDInference MeasureTheory ProbabilityTheory Matrix Pointwise in
/-- Corrected (fixed-shape), oracle-covariance variant of the confidence-set rule `eq:convex.Cdelta`
(`chapters/inference.tex:187–196`, display :191–193, claim "such sets serve as approximate confidence
regions" :196). See `docs/SOURCE-ISSUES.md#C47` and `#C43`.

Differs from the printed text: (1) the printed rule lets the convex set `𝒞_α` be chosen from the data
(through `V̄_T`, `Λ̂_T`), which is false in general (C47(1)); here the shape `K` is a convex set fixed before
the data and the region is the translate-and-scale `V̄_T + T^{-1/2} K` (the C47 proposed correction).
(2) The Gaussian reference is the oracle `N(0, Λ)`, `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (the population target of the
printed plug-in `Λ̂_T`, unknown in practice); `Γ_true` is the true residual covariance, not the printed `Γ`
(C43). The plug-in version with the same rate is the entry `Eq_convex_Cdelta_corrected_plugin`. (3) The rate is the printed `T^{-1/3}` of Theorem 7.11, but
with an instance constant `K₀` (it may depend on `M, π, μ, η₀, V₀`), not a printed coefficient. `Γ_true ≻ 0` is
assumed. Kept: i.i.d. sampling, full-support `μ`, `0 < η₀ < 1/4` (:133), every `V₀`.

Statement: one `K₀ > 0` such that for all `T ≥ 1` and every convex `K ⊆ ℝ^S`,
`|P(V^π ∈ V̄_T + T^{-1/2} K) − N(0, Λ)(K)| ≤ K₀ T^{-1/3}`. -/
def Eq_convex_Cdelta_fixedShape_corrected_oracle : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ T : ℕ, 1 ≤ T → ∀ K : Set (State → ℝ), Convex ℝ K →
      |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action |
            M.valueFixedPoint π ∈ prAverage M η₀ V₀ ω' +ᵥ (Real.sqrt T)⁻¹ • K}.indicator 1 ω) -
        (gaussCov (tdA M π μ) (trueGamma M π μ)).real K| ≤
        K₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))

open StatisticalRL StatisticalRL.Ch7Rest.TDInference MeasureTheory ProbabilityTheory Matrix in
/-- Corrected, oracle-covariance variant of the ellipsoid confidence region (`chapters/inference.tex:207–213`,
item (ii) of the rule `eq:convex.Cdelta` :187–196). See `docs/SOURCE-ISSUES.md#C47` (item (3)) and `#C43`.

Differs from the printed text: (1) the printed region `{V : T(V − V̄_T)ᵀ Λ̂_T⁻¹ (V − V̄_T) ≤ R²}` with `R` the
`1 − α` quantile of `χ²(d)` is compared with `R²`, although `R` is already on the `χ²` scale (C47(3)); here the threshold is `q` itself and the
Gaussian side is `N(0,Λ){x | xᵀΛ⁻¹x ≤ q}` (for the true `Λ` this is the `χ²(S)` probability of `[0, q]`; that
identification is not part of this entry but is proved in the separate entry
`Eq_convex_Cdelta_ellipsoid_corrected_oracle_chiSquared`; the existence of an exact `1 − α` threshold is the
separate entry `Eq_convex_Cdelta_ellipsoid_corrected_oracle_calibrated`). (2) The matrix is
the oracle `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (unknown in practice), not the plug-in `Λ̂_T`; `Γ_true` is the true
residual covariance (C43); under the hypotheses `Λ` is invertible, so `Λ⁻¹` is the genuine inverse. The plug-in
version, with the same rate, is `Eq_convex_Cdelta_ellipsoid_corrected_plugin`. (3) Rate `T^{-1/3}` as printed, with an instance constant `K₀` (it may depend on
`M, π, μ, η₀, V₀`). `Γ_true ≻ 0` is assumed. Kept: i.i.d. sampling, full-support `μ`, `0 < η₀ < 1/4` (:133), every `V₀`.

Statement: one `K₀ > 0` such that for all `T ≥ 1` and `q ≥ 0`, with `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`,
`|P(T (V^π − V̄_T)ᵀ Λ⁻¹ (V^π − V̄_T) ≤ q) − N(0,Λ){x | xᵀΛ⁻¹x ≤ q}| ≤ K₀ T^{-1/3}`. -/
def Eq_convex_Cdelta_ellipsoid_corrected_oracle : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ T : ℕ, 1 ≤ T → ∀ q : ℝ, 0 ≤ q →
      |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
            (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
              (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ)⁻¹ s s' ≤
              q}.indicator 1 ω) -
        (gaussCov (tdA M π μ) (trueGamma M π μ)).real
          {x | ∑ s, ∑ s', x s * x s' *
            ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ)⁻¹ s s' ≤ q}| ≤
        K₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))

open StatisticalRL StatisticalRL.Ch7Rest.TDInference MeasureTheory ProbabilityTheory Matrix in
/-- Corrected, oracle-covariance variant of the hyper-rectangle confidence region (`chapters/inference.tex:198–205`,
item (i) of the rule `eq:convex.Cdelta` :187–196). See `docs/SOURCE-ISSUES.md#C47` (item (2)) and `#C43`.

Differs from the printed text: (1) the printed half-width `R̂/√T`, with `R̂` the `ℓ∞` quantile under covariance
`Λ̂_T/T`, applies `√T` twice (C47(2)); here the half-width is `r/√T` with the Gaussian side
`N(0,Λ){x | ‖x‖∞ ≤ r}`, i.e. `r` is an `ℓ∞` level under covariance `Λ` (not `Λ/T`). (2) The covariance is the oracle
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (unknown in practice), not `Λ̂_T`; the plug-in version, with rate `T^{-1/3}`, is `Eq_convex_Cdelta_rectangle_corrected_plugin`;
`Γ_true` is the true residual covariance (C43). (3) Rate `T^{-1/3}` as printed, with an instance
constant `K₀` (it may depend on `M, π, μ, η₀, V₀`). `Γ_true ≻ 0` is assumed. The existence of an exact `1 − α` level `r` is not part of this entry
(see `Eq_convex_Cdelta_rectangle_corrected_oracle_calibrated`).
Kept: i.i.d. sampling, full-support `μ`, `0 < η₀ < 1/4` (:133), every `V₀`.

Statement: one `K₀ > 0` such that for all `T ≥ 1` and `r ≥ 0`,
`|P(∀ s, V̄_T(s) − r/√T ≤ V^π(s) ≤ V̄_T(s) + r/√T) − N(0,Λ){x | ∀ s, |x s| ≤ r}| ≤ K₀ T^{-1/3}`. -/
def Eq_convex_Cdelta_rectangle_corrected_oracle : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ T : ℕ, 1 ≤ T → ∀ r : ℝ, 0 ≤ r →
      |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          {ω' : Fin T → Tuple State Action | ∀ s,
            prAverage M η₀ V₀ ω' s - r / Real.sqrt T ≤ M.valueFixedPoint π s ∧
              M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + r / Real.sqrt T}.indicator 1 ω) -
        (gaussCov (tdA M π μ) (trueGamma M π μ)).real {x | ∀ s, |x s| ≤ r}| ≤
        K₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))

open StatisticalRL StatisticalRL.Ch7Rest.TDInference MeasureTheory ProbabilityTheory Matrix in
/-- Calibrated, corrected, oracle-covariance variant of the ellipsoid confidence region
(`chapters/inference.tex:207–213`, item (ii) of the rule `eq:convex.Cdelta` :187–196). See
`docs/SOURCE-ISSUES.md#C47` (item (3)) and `#C43`.

Differs from the printed text exactly as `Eq_convex_Cdelta_ellipsoid_corrected_oracle`: (1) corrected shape,
threshold `q` compared with `T (V − V̄_T)ᵀ Λ⁻¹ (V − V̄_T)` instead of the printed `R²` (C47(3)); (2) oracle
covariance `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (unknown in practice), not the plug-in `Λ̂_T`; `Γ_true` is the true residual
covariance (C43); (3) rate `T^{-1/3}` as printed, with an instance constant
`K₀` (it may depend on `M, π, μ, η₀, V₀`, but not on `α`). In addition to that entry, for every `α ∈ (0,1)` an
exact Gaussian `1 − α` level `q_α ≥ 0` exists, `N(0,Λ){x | xᵀΛ⁻¹x ≤ q_α} = 1 − α`, and the coverage is within
`K₀ T^{-1/3}` of `1 − α`. This entry only asserts that the level exists; its identification with the
`χ²(S)` `(1 − α)`-quantile is the separate entry `Eq_convex_Cdelta_ellipsoid_corrected_oracle_chiSquared`
(threshold `R`, not the printed `R²`). These are not the printed formulas; the plug-in versions (with `Λ̂_T`) are the entries `Eq_convex_Cdelta_ellipsoid_corrected_plugin` and `Eq_convex_Cdelta_rectangle_corrected_plugin`, also with rate `T^{-1/3}`.
`Γ_true ≻ 0` is assumed. Kept: i.i.d. sampling, full-support `μ`, `0 < η₀ < 1/4` (:133), every `V₀`.

Statement: one `K₀ > 0` such that for every `α ∈ (0,1)` there is `q ≥ 0` with `N(0,Λ){x | xᵀΛ⁻¹x ≤ q} = 1 − α`
and, for all `T ≥ 1`, `|P(T (V^π − V̄_T)ᵀ Λ⁻¹ (V^π − V̄_T) ≤ q) − (1 − α)| ≤ K₀ T^{-1/3}`. -/
def Eq_convex_Cdelta_ellipsoid_corrected_oracle_calibrated : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ α : ℝ, 0 < α → α < 1 → ∃ q : ℝ, 0 ≤ q ∧
      (gaussCov (tdA M π μ) (trueGamma M π μ)).real
          {x | ∑ s, ∑ s', x s * x s' *
            ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ)⁻¹ s s' ≤ q} = 1 - α ∧
      ∀ T : ℕ, 1 ≤ T →
        |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
              (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
                (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                  ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ)⁻¹ s s' ≤
                q}.indicator 1 ω) - (1 - α)| ≤
          K₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))

open StatisticalRL StatisticalRL.Ch7Rest.TDInference MeasureTheory ProbabilityTheory Matrix in
/-- Calibrated, corrected, oracle-covariance variant of the hyper-rectangle confidence region
(`chapters/inference.tex:198–205`, item (i) of the rule `eq:convex.Cdelta` :187–196). See
`docs/SOURCE-ISSUES.md#C47` (item (2)) and `#C43`.

Differs from the printed text exactly as `Eq_convex_Cdelta_rectangle_corrected_oracle`: (1) corrected shape,
half-width `r/√T` with `r` an `ℓ∞` level under covariance `Λ` (the printed `R̂/√T` applies `√T` twice, C47(2));
(2) oracle covariance `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (unknown in practice), not `Λ̂_T`; `Γ_true` is the true
residual covariance (C43); (3) rate `T^{-1/3}` as printed, with an
instance constant `K₀` (it may depend on `M, π, μ, η₀, V₀`, but not on `α`). In addition to that entry, for every `α ∈ (0,1)` an exact Gaussian
`1 − α` level `r_α ≥ 0` exists, `N(0,Λ){x | ∀ s, |x s| ≤ r_α} = 1 − α`, and the coverage is within
`K₀ T^{-1/3}` of `1 − α`. The level is only shown to exist: it is not identified with the printed `ℓ∞`
quantile formula. These are not the printed formulas; the plug-in versions (with `Λ̂_T`) are the entries `Eq_convex_Cdelta_ellipsoid_corrected_plugin` and `Eq_convex_Cdelta_rectangle_corrected_plugin`, also with rate `T^{-1/3}`.
`Γ_true ≻ 0` is assumed. Kept: i.i.d. sampling, full-support `μ`, `0 < η₀ < 1/4` (:133), every `V₀`.

Statement: one `K₀ > 0` such that for every `α ∈ (0,1)` there is `r ≥ 0` with `N(0,Λ){x | ∀ s, |x s| ≤ r} = 1 − α`
and, for all `T ≥ 1`, `|P(∀ s, V̄_T(s) − r/√T ≤ V^π(s) ≤ V̄_T(s) + r/√T) − (1 − α)| ≤ K₀ T^{-1/3}`. -/
def Eq_convex_Cdelta_rectangle_corrected_oracle_calibrated : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ α : ℝ, 0 < α → α < 1 → ∃ r : ℝ, 0 ≤ r ∧
      (gaussCov (tdA M π μ) (trueGamma M π μ)).real {x | ∀ s, |x s| ≤ r} = 1 - α ∧
      ∀ T : ℕ, 1 ≤ T →
        |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∀ s,
              prAverage M η₀ V₀ ω' s - r / Real.sqrt T ≤ M.valueFixedPoint π s ∧
                M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + r / Real.sqrt T}.indicator 1 ω) -
          (1 - α)| ≤
          K₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))

open StatisticalRL StatisticalRL.Ch7Rest.TDInference MeasureTheory ProbabilityTheory Matrix in
/-- Corrected, oracle-covariance ellipsoid confidence region at the printed `χ²(S)` quantile
(`chapters/inference.tex:207–213`, item (ii) of the rule `eq:convex.Cdelta` :187–196). See
`docs/SOURCE-ISSUES.md#C47` (item (3)) and `#C43`.

Differs from the printed text: (1) the threshold is the `χ²(S)` `(1 − α)`-quantile `R` itself, not the printed
`R²` (`R` is already on the `χ²` scale, C47(3)); `d = S = |State|`. (2) The matrix is the oracle
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (unknown in practice), not the plug-in `Λ̂_T`; `Γ_true` is the true residual
covariance (C43); the plug-in version with the same rate is `Eq_convex_Cdelta_ellipsoid_corrected_plugin`. (3) Rate `T^{-1/3}` as printed, with an
instance constant `K₀` (it may depend on `M, π, μ, η₀, V₀`, but not on `α` or `R`).
`Γ_true ≻ 0` is assumed. Kept: i.i.d. sampling, full-support `μ`, `0 < η₀ < 1/4` (:133), every `V₀`.
`χ²(S)` is written out as Mathlib's gamma law `gammaMeasure (S/2) (1/2)` (shape `S/2`, rate `1/2`).

Statement: one `K₀ > 0` such that for every `α ∈ (0,1)` a `χ²(S)` `(1 − α)`-quantile `R ≥ 0` exists, and for
every `R` with `F_{χ²(S)}(R) = 1 − α`: `N(0,Λ){x | xᵀΛ⁻¹x ≤ R} = 1 − α` and, for all `T ≥ 1`,
`|P(T (V^π − V̄_T)ᵀ Λ⁻¹ (V^π − V̄_T) ≤ R) − (1 − α)| ≤ K₀ T^{-1/3}`. -/
def Eq_convex_Cdelta_ellipsoid_corrected_oracle_chiSquared : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ α : ℝ, 0 < α → α < 1 →
      (∃ R : ℝ, 0 ≤ R ∧ cdf (gammaMeasure ((Fintype.card State : ℝ) / 2) (1 / 2)) R = 1 - α) ∧
      ∀ R : ℝ, cdf (gammaMeasure ((Fintype.card State : ℝ) / 2) (1 / 2)) R = 1 - α →
        (gaussCov (tdA M π μ) (trueGamma M π μ)).real
            {x | ∑ s, ∑ s', x s * x s' *
              ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ)⁻¹ s s' ≤ R} = 1 - α ∧
        ∀ T : ℕ, 1 ≤ T →
          |(∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
              {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
                (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
                  (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                    ((tdA M π μ)⁻¹ * diagonal (trueGamma M π μ) * (tdA M π μ)⁻¹ᵀ)⁻¹ s s' ≤
                  R}.indicator 1 ω) - (1 - α)| ≤
            K₀ * (T : ℝ) ^ (-(1 / 3 : ℝ))

open StatisticalRL StatisticalRL.Ch7Rest.TDInference MeasureTheory ProbabilityTheory Matrix in
/-- Corrected plug-in ellipsoid (`chapters/inference.tex:207–213`, item (ii) of `eq:convex.Cdelta`
:187–196; `Λ̂_T` :180–182), finite-`T` rate. See `docs/SOURCE-ISSUES.md#C47` ((3), (4)) and `#C43`.
Differs: threshold `R` (the `χ²(S)` quantile), not `R²` (C47(3)), `d = S`; instance constant `K`
(independent of `T`, `q`, `α`, `R`), rate `T^{-1/3}`; added `Γ_true ≻ 0`; target per C43; junk inverse
`Λ̂_T⁻¹ = 0` on singular outcomes, inside the charged bad event (C47(4)). `χ²(S)` is
`gammaMeasure (S/2) (1/2)`. Kept: i.i.d. sampling, full-support `μ`, `0 < η₀ < 1/4`, every `V₀`. -/
def Eq_convex_Cdelta_ellipsoid_corrected_plugin : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K : ℝ, 0 < K ∧
      (∀ T : ℕ, 1 ≤ T → ∀ q : ℝ,
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
              (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
                (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                  (lambdaHat M η₀ V₀ ω')⁻¹ s s' ≤ q}.indicator 1 ω -
          cdf (gammaMeasure ((Fintype.card State : ℝ) / 2) (1 / 2)) q| ≤
          K * (T : ℝ) ^ (-(1 / 3 : ℝ))) ∧
      (∀ α : ℝ, 0 < α → α < 1 → ∀ R : ℝ,
        cdf (gammaMeasure ((Fintype.card State : ℝ) / 2) (1 / 2)) R = 1 - α →
        ∀ T : ℕ, 1 ≤ T →
          |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
              {ω' : Fin T → Tuple State Action | (T : ℝ) * ∑ s, ∑ s',
                (M.valueFixedPoint π s - prAverage M η₀ V₀ ω' s) *
                  (M.valueFixedPoint π s' - prAverage M η₀ V₀ ω' s') *
                    (lambdaHat M η₀ V₀ ω')⁻¹ s s' ≤ R}.indicator 1 ω - (1 - α)| ≤
            K * (T : ℝ) ^ (-(1 / 3 : ℝ)))

open StatisticalRL StatisticalRL.Ch7Rest.TDInference MeasureTheory ProbabilityTheory Matrix in
/-- Corrected plug-in hyper-rectangle (`chapters/inference.tex:198–205`, item (i) of
`eq:convex.Cdelta` :187–196; `Λ̂_T` :180–182), finite-`T` rate. See `docs/SOURCE-ISSUES.md#C47`
((2), (4)) and `#C43`. Differs: half-width `r̂_T/√T`, `r̂_T` a `(1 − α)` quantile of `‖X‖∞`,
`X ~ N(0, Λ̂_T)` (not the printed double-`√T` scaling, C47(2)); `K` depends on the instance AND on `α`
(through `min(α, 1 − α)`), not on `T` or the quantile choice; rate `T^{-1/3}`; added `Γ_true ≻ 0`;
target per C43; junk `Λ̂_T = 0` (so `r̂_T = 0`) on the singular event, charged (C47(4)).
`N(0, Λ̂_T)` is the law of `Q Z`, `Q Qᵀ = Λ̂_T`. Kept: i.i.d. sampling, full-support `μ`,
`0 < η₀ < 1/4`, every `V₀`, `α ∈ (0,1)`. -/
def Eq_convex_Cdelta_rectangle_corrected_plugin : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∀ α : ℝ, 0 < α → α < 1 →
    (∃ rhat : (T : ℕ) → (Fin T → Tuple State Action) → ℝ,
      ∀ (T : ℕ) (ω : Fin T → Tuple State Action), ∃ Q : Matrix State State ℝ,
        Q * Qᵀ = lambdaHat M η₀ V₀ ω ∧
        (∀ r : ℝ, ((Measure.pi fun _ : State ↦ gaussianReal 0 1).map (Q *ᵥ ·)).real
            {x | ∀ s, |x s| ≤ r} < 1 - α → r ≤ rhat T ω) ∧
        (∀ r : ℝ, 1 - α < ((Measure.pi fun _ : State ↦ gaussianReal 0 1).map (Q *ᵥ ·)).real
            {x | ∀ s, |x s| ≤ r} → rhat T ω ≤ r)) ∧
    ∃ K : ℝ, 0 < K ∧ ∀ rhat : (T : ℕ) → (Fin T → Tuple State Action) → ℝ,
      (∀ (T : ℕ) (ω : Fin T → Tuple State Action), ∃ Q : Matrix State State ℝ,
        Q * Qᵀ = lambdaHat M η₀ V₀ ω ∧
        (∀ r : ℝ, ((Measure.pi fun _ : State ↦ gaussianReal 0 1).map (Q *ᵥ ·)).real
            {x | ∀ s, |x s| ≤ r} < 1 - α → r ≤ rhat T ω) ∧
        (∀ r : ℝ, 1 - α < ((Measure.pi fun _ : State ↦ gaussianReal 0 1).map (Q *ᵥ ·)).real
            {x | ∀ s, |x s| ≤ r} → rhat T ω ≤ r)) →
      ∀ T : ℕ, 1 ≤ T →
        |∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
            {ω' : Fin T → Tuple State Action | ∀ s,
              prAverage M η₀ V₀ ω' s - rhat T ω' / Real.sqrt T ≤ M.valueFixedPoint π s ∧
                M.valueFixedPoint π s ≤ prAverage M η₀ V₀ ω' s + rhat T ω' / Real.sqrt T}.indicator
              1 ω - (1 - α)| ≤ K * (T : ℝ) ^ (-(1 / 3 : ℝ))

end EqConvexCdelta

section EqDefnHatLambda

open StatisticalRL StatisticalRL.Ch7Rest.TDInference in
/-- Corrected `eq:defn-hat-Lambda` (`chapters/inference.tex:180–182`; "the final estimator of
`Λ⋆`" :184; `Ā_T`, `Γ̂_T` :165–169, "as estimators of `A` and `Γ`" :172, weights :175–177), read as
consistency. Differs from the printed claim: the target is `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ` (true
TD-noise covariance), not the printed `Λ⋆ = A⁻¹ΓA⁻ᵀ`; under action-dependent rewards with
`r(s) = r_π(s)` the printed reading is false, from every `V₀` (`docs/SOURCE-ISSUES.md#C43`). For
every finite instance with full-support i.i.d. sampling (`λ₀ > 0`, :67), every `0 < η₀ < 1/4`
(:133) and every `V₀`, `Λ̂_T → Λ` entrywise in probability. No `Γ_true ≻ 0` is assumed.
Qualitative: no rate. Junk value: on the event that some state is unsampled, `Ā_T` is singular and
the printed `Λ̂_T` is undefined (`docs/SOURCE-ISSUES.md#C47`(4)); Lean's `Matrix.inv` returns 0
there, so `lambdaHat = 0` on that event, whose probability `≤ ∑_s (1 − μ(s))^T` tends to 0. -/
def Eq_defn_hat_Lambda_corrected : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 →
    ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto (fun T : ℕ ↦ pathProb M π μ T
        {ω | ∃ s s', ε < |lambdaHat M η₀ V₀ ω s s' - trueLambda M π μ s s'|})
        Filter.atTop (nhds 0)

open StatisticalRL StatisticalRL.Ch7Rest.TDInference in
/-- Restricted `eq:defn-hat-Lambda` (`chapters/inference.tex:180–182`; "the final estimator of
`Λ⋆`" :184; `Λ⋆ = A⁻¹ΓA⁻ᵀ`, `A`, `Γ` :99–117 with `r(s) = r_π(s)`), read as consistency for the
printed `Λ⋆`, restricted to instances where `r(s,·)` is constant on the support of `π(·|s)` for
every state `s` (state-only rewards or deterministic `π`), where `Γ_printed = Γ_true`. Differs
from the printed claim only by this restriction of the MDP class: outside it, under
action-dependent rewards with `r(s) = r_π(s)`, the printed reading is false from every `V₀`
(`docs/SOURCE-ISSUES.md#C43`). Full-support i.i.d. sampling, `0 < η₀ < 1/4` (:133), every `V₀`;
no `Γ ≻ 0` is assumed. Qualitative: no rate. Junk value as in `Eq_defn_hat_Lambda_corrected`
(`docs/SOURCE-ISSUES.md#C47`(4)). -/
def Eq_defn_hat_Lambda_restricted : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s a a', 0 < (π s).prob a → 0 < (π s).prob a' → M.reward s a = M.reward s a') →
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 →
    ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto (fun T : ℕ ↦ pathProb M π μ T
        {ω | ∃ s s', ε < |lambdaHat M η₀ V₀ ω s s' - printedLambda M π μ s s'|})
        Filter.atTop (nhds 0)

end EqDefnHatLambda

section Thm7_12

open StatisticalRL.Ch7Rest.Rlhf in
/-- Corrected Theorem 7.12, `thm_online`, `chapters/RLHF.tex:208–215` (online VPO,
Algorithm `alg:online_RBMLE` :182–203; setup :21–59, :92–102, linear rewards
`assump:linear` :146–153; `docs/SOURCE-ISSUES.md#C44`). Corrected, well-posed variant.

Setting: finite prompts `X` with probability vector `ρ`, finite answers `Y`, reference policy
`π_ref` with full support, calibration policy `π_cal` (any conditional policy), features
`φ : X → Y → ℝ^d` with `‖φ‖₂ ≤ 1` and `d ≥ 1`, true parameter `θ⋆` with `‖θ⋆‖₂ ≤ r_max`,
`β, r_max, α, δ > 0`, horizon `T ≥ 1`. Round `t` (0-indexed `k = t − 1` in Lean) draws
`x ∼ ρ`, `y₁, y₂ ∼ π^{(t)}(·|x)` independently and a Bradley–Terry label with reward
`r⋆ = ⟪φ, θ⋆⟫`; `π^{(t)}` is the Gibbs policy of `sel (D^{(t−1)})`, where `D^{(t−1)}` lists the
comparisons of rounds `1..t−1` (:162, :196). The law of the `T` rounds is the finite product
`vpoTrajWeight`, and the probability of an event is the weighted sum over all trajectories; the
weights are nonnegative and sum to one (`StatisticalRL.Ch7Rest.Rlhf.vpoTrajWeight_nonneg`,
`StatisticalRL.Ch7Rest.Rlhf.vpoTrajWeight_sum`).
`Regret = ∑_{t=1}^{T} [J⋆(r⋆; π_cal) − J(r⋆, π^{(t)}; π_cal)]` with `J` the calibrated value
(:92–96) and `J⋆` its supremum over all conditional policies (:99–102);
`κ = sup_{x,y} π_cal(y|x)/π_ref(y|x)` (:214).

Conclusion: (a) a ball-constrained selection rule exists; (b) for every such rule and every
`α > 0`, with probability at least `1 − δ`, `Regret ≤ T·B′/α + K·Γ·α`, where
`B′ = 2 log(2T/δ) + 2d log⌈2 r_max T √d⌉₊ + 4`, `Γ = (e/(e−1)) (2d log(1 + T/d) + log(2/δ))`,
`K = 2κ e^{4 r_max + 2 r_max/β}`.

Differences from the printed statement:
(i) the update is the printed VPO objective (:194–198, `vpoObjective`) minimized over the Gibbs
policies `{π_θ : ‖θ‖₂ ≤ r_max}` (any minimizer; `IsBallSelection`), because the printed argmin
over all policies need not exist (C44). This covers every printed run whose iterates exist with
`‖θ^{(t)}‖ ≤ r_max`: the rule "the unconstrained Gibbs minimizer if one exists in the ball, else
any ball minimizer" is an admissible selection rule, and the statement quantifies over every rule
(when the printed argmin's tie-breaking is a deterministic function of the dataset; the objective
is not convex in `θ`, so ties are possible, and randomized or external tie-breaking is not covered.
This subsumption is an informal remark, not part of the formal statement; only its dataset-level
extension step was machine-checked, in an independent review probe);
(ii) `X` and `Y` are finite (the source allows a general prompt distribution `ρ`);
(iii) any `α > 0` and `T ≥ 1` (the printed `α` (:214) is undefined at `T = 1` and is one
admissible instance for `T ≥ 2`);
(iv) `δ` appears explicitly in the bound;
(v) the conclusion is the explicit bound above, which at the tuned `α` is
`O(e^{2 r_max + r_max/β} d √(κT) · log)` (informal arithmetic, not formalized). The printed rate `Õ(e^{2 r_max + r_max/β} √(κ d T))` is
neither proved nor refuted here. -/
def Thm7_12_corrected : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (d T : ℕ) (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ)
    (φ : X → Y → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (β r_max α δ : ℝ),
    0 < d → 1 ≤ T → (∀ x, 0 ≤ ρ x) → ∑ x, ρ x = 1 →
    IsPositivePolicy π_ref → IsCondPolicy π_cal → (∀ x y, ‖φ x y‖ ≤ 1) →
    0 < β → 0 < r_max → ‖θstar‖ ≤ r_max → 0 < α → 0 < δ →
    (∃ sel, IsBallSelection ρ π_ref π_cal φ α β r_max sel) ∧
    ∀ sel, IsBallSelection ρ π_ref π_cal φ α β r_max sel →
      1 - δ ≤ ∑ h : Fin T → X × Y × Y × Bool, vpoTrajWeight ρ π_ref φ θstar β sel h *
        (if vpoRegret ρ π_ref π_cal φ θstar β sel h ≤
            T * (2 * Real.log (2 * T / δ) +
                2 * d * Real.log ⌈2 * r_max * T * Real.sqrt (d : ℝ)⌉₊ + 4) / α +
              2 * vpoKappa π_ref π_cal * Real.exp (4 * r_max + 2 * r_max / β) *
                (Real.exp 1 / (Real.exp 1 - 1) *
                  (2 * d * Real.log (1 + T / d) + Real.log (2 / δ))) * α
          then 1 else 0)

open StatisticalRL.Ch7Rest.Rlhf in
/-- Corrected Theorem 7.12, local-curvature form (`thm_online`, `chapters/RLHF.tex:208–215`;
`docs/SOURCE-ISSUES.md#C44`). Same setting, hypotheses and differences (i)–(iv) as
`Thm7_12_corrected`; the conclusion (b) is instead the bound
`Regret ≤ (e^{4 r_max/β}/(4β)) · (16 r_max² + 16 e^{4 r_max} (B′ + 4 r_max α)) · Γ`
(with the same `B′`, `Γ`), which does not involve `κ`. Informally (arithmetic on this bound, not
formalized), at the printed `α` (`T ≥ 2`) its `(d, T)` scaling is `Õ(√(dT))` once `T ≳ d³`, with
constants (`e^{2 r_max + 3 r_max/β} r_max/β` and an additive `e^{4 r_max + 4 r_max/β} d² log² T/β`)
different from the printed ones. The printed rate
`Õ(e^{2 r_max + r_max/β} √(κ d T))` is neither proved nor refuted here. -/
def Thm7_12_corrected_local : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (d T : ℕ) (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ)
    (φ : X → Y → EuclideanSpace ℝ (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (β r_max α δ : ℝ),
    0 < d → 1 ≤ T → (∀ x, 0 ≤ ρ x) → ∑ x, ρ x = 1 →
    IsPositivePolicy π_ref → IsCondPolicy π_cal → (∀ x y, ‖φ x y‖ ≤ 1) →
    0 < β → 0 < r_max → ‖θstar‖ ≤ r_max → 0 < α → 0 < δ →
    (∃ sel, IsBallSelection ρ π_ref π_cal φ α β r_max sel) ∧
    ∀ sel, IsBallSelection ρ π_ref π_cal φ α β r_max sel →
      1 - δ ≤ ∑ h : Fin T → X × Y × Y × Bool, vpoTrajWeight ρ π_ref φ θstar β sel h *
        (if vpoRegret ρ π_ref π_cal φ θstar β sel h ≤
            Real.exp (4 * r_max / β) / (4 * β) *
              (16 * r_max ^ 2 + 16 * Real.exp (4 * r_max) *
                ((2 * Real.log (2 * T / δ) +
                  2 * d * Real.log ⌈2 * r_max * T * Real.sqrt (d : ℝ)⌉₊ + 4) + 4 * r_max * α)) *
              (Real.exp 1 / (Real.exp 1 - 1) *
                (2 * d * Real.log (1 + T / d) + Real.log (2 / δ)))
          then 1 else 0)

end Thm7_12

section Eq_DPO_VPO

open StatisticalRL.Ch7Rest.Rlhf in
/-- Restricted `eq:DPO`, `chapters/RLHF.tex:62–74` (with the reward–policy correspondence
`eq:reward-policy-eq` :63–66, the Gibbs closed form `eq:RLHF-policy-closed-form` :52–59, the
cancellation of `Z(r, x)` :74 and the prompt-shift non-identifiability :90). For finite prompts `X`,
finite answers `Y`, a full-support reference policy `π_ref`, `β > 0` and any dataset `D` of
comparisons `(x, y₊, y₋)`, with `ℓ(r, D) = −∑ log σ(r(x,y₊) − r(x,y₋))` and
`DPO(π) = −∑ log σ(β (log π(y₊|x)/π_ref(y₊|x) − log π(y₋|x)/π_ref(y₋|x)))`:
(i) `DPO(π_r) = ℓ(r, D)` for every reward `r` (`Z` cancels);
(ii) every full-support policy is a Gibbs policy `π_r` (`r = β log(π/π_ref)`, `eq:reward-policy-eq`);
(iii) `π_r = π_{r'}` iff `r − r'` depends on the prompt only;
(iv) a full-support `π` minimizes `DPO` over full-support policies iff `π = π_r` for some
minimizer `r` of `ℓ(·, D)` (existence of minimizers is not claimed).

Restriction (`docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`): the argmin in `eq:DPO` is
taken over full-support policies (`IsPositivePolicy`), not over all policies. This is the
substantive restriction: in the source's extended-real reading a policy with `π(y₋|x) = 0` has
`−log σ(+∞) = 0`, so over all policies the minimum `0` can be attained only at boundary policies,
which are not Gibbs policies, while over full-support policies the infimum `0` is unattained and no
reward MLE exists (e.g. a dataset whose only comparison is `(x, y₁, y₂)`); in Lean, `log 0 = 0`
gives such a boundary policy the junk loss `−log σ(β log(π(y₁|x)/π_ref(y₁|x)))` instead of `0`. The book's derivation works with
the Gibbs policies `π_r`, which have full support. Also: `π_ref` has full support (implicit in the
source, where `log π_ref` appears in `eq:reward-policy-eq`), and `X`, `Y` are finite (the source's
`Z(r, x)` is a finite sum over `Y`). -/
def Eq_DPO_restricted : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (π_ref : X → Y → ℝ) (β : ℝ) (D : List (X × Y × Y)),
    IsPositivePolicy π_ref → 0 < β →
    let nll : (X → Y → ℝ) → ℝ := fun r ↦
      -(D.map fun z ↦ Real.log (Real.sigmoid (r z.1 z.2.1 - r z.1 z.2.2))).sum
    let dpo : (X → Y → ℝ) → ℝ := fun π ↦
      -(D.map fun z ↦ Real.log (Real.sigmoid
          (β * (Real.log (π z.1 z.2.1 / π_ref z.1 z.2.1) -
                Real.log (π z.1 z.2.2 / π_ref z.1 z.2.2))))).sum
    (∀ r, dpo (gibbsPolicy π_ref r β) = nll r) ∧
    (∀ π, IsPositivePolicy π → ∃ r, π = gibbsPolicy π_ref r β) ∧
    (∀ r r', gibbsPolicy π_ref r β = gibbsPolicy π_ref r' β ↔
      ∃ c : X → ℝ, ∀ x y, r x y = r' x y + c x) ∧
    (∀ π, IsPositivePolicy π →
      ((∀ π', IsPositivePolicy π' → dpo π ≤ dpo π') ↔
        ∃ r, π = gibbsPolicy π_ref r β ∧ ∀ r', nll r ≤ nll r'))

open StatisticalRL.Ch7Rest.Rlhf in
/-- Restricted `eq:policy_RBMLE`, `chapters/RLHF.tex:115–141` (`eq:RBMLE` :107–113, `eq:Jstar`
:116–124, the `π_ref → π_cal` swap and KL identity :137–140). For the VPO objective
`vpoObjective` with coefficient `sign·α` (`sign ∈ {1, −1}`, `α > 0`, `β > 0`, `ρ ≥ 0`, full-support
`π_ref`, any conditional policy `π_cal`), and the reward-space objective
`obj(r) = ℓ(r, D) − sign·α·J⋆(r; π_cal)` with `J⋆` the supremum of the calibrated value over all
conditional policies (`optCalValue`):
(i) `obj(r)` equals the VPO objective at the Gibbs policy `π_r` (lines :126–131);
(ii) a full-support `π` minimizes the VPO objective over full-support policies iff `π = π_r` for
some minimizer `r` of `obj` (:131–133; existence of minimizers is not claimed);
(iii) `E_{ρ,π_cal}[log π − log π_cal] = −E_ρ KL(π_cal‖π)` for full-support `π` (:138–140, with
`0 log 0 = 0`);
(iv) replacing `π_ref` by `π_cal` in the last term of the objective (DPO part unchanged) shifts the
objective by a constant `K` independent of `π`, so it does not change the minimizers (:137).

Restricted as `Eq_DPO_restricted` (argmin over full-support policies; full-support `π_ref`; finite
`X`, `Y`; `docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`). -/
def Eq_policy_RBMLE_restricted : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ)
    (sign α β : ℝ) (D : List (X × Y × Y)),
    IsPositivePolicy π_ref → (∀ x, 0 ≤ ρ x) → IsCondPolicy π_cal →
    0 < β → 0 < α → (sign = 1 ∨ sign = -1) →
    let nll : (X → Y → ℝ) → ℝ := fun r ↦
      -(D.map fun z ↦ Real.log (Real.sigmoid (r z.1 z.2.1 - r z.1 z.2.2))).sum
    let obj : (X → Y → ℝ) → ℝ := fun r ↦ nll r - sign * α * optCalValue ρ π_ref π_cal β r
    (∀ r, obj r = vpoObjective ρ π_ref π_cal (sign * α) β D (gibbsPolicy π_ref r β)) ∧
    (∀ π, IsPositivePolicy π →
      ((∀ π', IsPositivePolicy π' →
          vpoObjective ρ π_ref π_cal (sign * α) β D π ≤
            vpoObjective ρ π_ref π_cal (sign * α) β D π') ↔
        ∃ r, π = gibbsPolicy π_ref r β ∧ ∀ r', obj r ≤ obj r')) ∧
    (∀ π, IsPositivePolicy π →
      ∑ x, ρ x * ∑ y, π_cal x y * (Real.log (π x y) - Real.log (π_cal x y)) =
        -∑ x, ρ x * klDiv (π_cal x) (π x)) ∧
    (∃ K : ℝ, ∀ π, IsPositivePolicy π →
      vpoObjective ρ π_ref π_cal (sign * α) β D π =
        (-(D.map fun z ↦ Real.log (Real.sigmoid
            (β * Real.log (π z.1 z.2.1 / π_ref z.1 z.2.1) -
              β * Real.log (π z.1 z.2.2 / π_ref z.1 z.2.2)))).sum +
          sign * α * β * ∑ x, ρ x * ∑ y, π_cal x y *
            (Real.log (π x y) - Real.log (π_cal x y))) + K)

open StatisticalRL.Ch7Rest.Rlhf in
/-- Restricted `eq:online_RBMLE`, `chapters/RLHF.tex:158–198` (reward-learning step
`eq:RBMLE_online` :163–170, policy-learning step `eq:RLHF-policy` :172–175, the combination claim
:177, the update :194–198 with `sign = +1`; the dataset `D` is arbitrary, covering `D^{(t)}`).
For `α, β > 0`, `ρ ≥ 0`, full-support `π_ref`, any conditional policy `π_cal`, and every minimizer
`r` of `ℓ(r, D) − α J⋆(r; π_cal)` (`J⋆` = supremum of the calibrated value over all conditional
policies, `optCalValue`):
(a) the Gibbs policy `π_r` solves the policy-learning step `eq:RLHF-policy`: it maximizes the
printed KL-regularized value `J(r, π) = E_{x∼ρ, y∼π}[r] − β E_ρ KL(π(·|x)‖π_ref(·|x))` of
`eq:KL_reward` (:41–45), written inline, over all conditional policies;
(b) `π_r` minimizes the online VPO objective of `eq:online_RBMLE` over full-support policies
(`IsVPOMinimizer`).
Uniqueness (every maximizer of `J(r, ·)` equals `π_r`) is not claimed: it fails off the support
of `ρ`, and the combination claim does not need it. Existence of a minimizer `r` is not claimed
(`docs/SOURCE-ISSUES.md#C44`).

Restricted as `Eq_DPO_restricted` (argmin over full-support policies; full-support `π_ref`; finite
`X`, `Y`; `docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`). -/
def Eq_online_RBMLE_restricted : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ)
    (α β : ℝ) (D : List (X × Y × Y)),
    IsPositivePolicy π_ref → (∀ x, 0 ≤ ρ x) → IsCondPolicy π_cal → 0 < β → 0 < α →
    let obj : (X → Y → ℝ) → ℝ := fun r ↦
      -(D.map fun z ↦ Real.log (Real.sigmoid (r z.1 z.2.1 - r z.1 z.2.2))).sum -
        α * optCalValue ρ π_ref π_cal β r
    ∀ r, (∀ r', obj r ≤ obj r') →
      (∀ π, IsCondPolicy π →
        ∑ x, ρ x * (∑ y, π x y * r x y - β * klDiv (π x) (π_ref x)) ≤
          ∑ x, ρ x * (∑ y, gibbsPolicy π_ref r β x y * r x y -
            β * klDiv (gibbsPolicy π_ref r β x) (π_ref x))) ∧
      IsVPOMinimizer ρ π_ref π_cal α β D (gibbsPolicy π_ref r β)

end Eq_DPO_VPO

section RLHFDisplays

open StatisticalRL.Ch7Rest.Rlhf in
/-- Restricted `eq:reward-policy-eq`, `chapters/RLHF.tex:62–66`, with `π_r` the Gibbs policy of
`eq:RLHF-policy-closed-form` (`:52–55`), `π_r(y|x) = π_ref(y|x) exp(r(x,y)/β) / Z(r,x)`
(`gibbsPolicy`), and `Z(r,x)` of `eq:normalization` (`:56–59`) written out:
for every reward `r` and all `(x, y)`,
`r(x,y) = β (log π_r(y|x) − log π_ref(y|x) + log Z(r,x))`.

Restricted as `Eq_DPO_restricted`: full-support `π_ref` (implicit in the source, where
`log π_ref` appears) and finite `X`, `Y` (the source's `Z(r,x)` is a finite sum over `Y`)
(`docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`). -/
def Eq_reward_policy_eq_restricted : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (π_ref : X → Y → ℝ) (β : ℝ),
    IsPositivePolicy π_ref → 0 < β →
    ∀ (r : X → Y → ℝ) (x : X) (y : Y),
      r x y = β * (Real.log (gibbsPolicy π_ref r β x y) - Real.log (π_ref x y) +
        Real.log (∑ y', π_ref x y' * Real.exp (r x y' / β)))

open StatisticalRL.Ch7Rest.Rlhf in
/-- Restricted `eq:Jstar`, `chapters/RLHF.tex:115–124`: all four printed expressions of
`J⋆(r; π_cal)` (`eq:Jstar_calibrated`, `:99–102`, the supremum of the calibrated value
`eq:calibrated_value` (`chapters/RLHF.tex:92–96`) over all conditional policies, `optCalValue`), with `π_r` the Gibbs policy
`π_r(y|x) = π_ref(y|x) exp(r(x,y)/β) / Z(r,x)` (`gibbsPolicy`) and `Z(r,x) = ∑_{y'} π_ref(y'|x) exp(r(x,y')/β)` (`eq:normalization`, `:56–59`) written out:
first line `E_{ρ,π_r}[r − β(log π_r − log π_ref)] − E_{ρ,π_cal} r` (:118–119), second line
`β E_ρ log Z(r,·) − E_{ρ,π_cal} r` (:120), (i) `E_{ρ,π_cal}[β log Z(r,x) − r(x,y)]` (:121) and
(ii) `−β E_{ρ,π_cal}[log π_r − log π_ref]` (:122). Step (i) uses that `π_cal(·|x)` sums to one
(`IsCondPolicy π_cal`); `ρ ≥ 0` suffices (no normalization of `ρ` is used).

Restricted as `Eq_DPO_restricted`: full-support `π_ref`, finite `X`, `Y`
(`docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`). -/
def Eq_Jstar_restricted : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ) (β : ℝ),
    IsPositivePolicy π_ref → (∀ x, 0 ≤ ρ x) → IsCondPolicy π_cal → 0 < β →
    ∀ r : X → Y → ℝ,
      (optCalValue ρ π_ref π_cal β r =
          ∑ x, ρ x * ∑ y, gibbsPolicy π_ref r β x y *
            (r x y - β * (Real.log (gibbsPolicy π_ref r β x y) - Real.log (π_ref x y))) -
          ∑ x, ρ x * ∑ y, π_cal x y * r x y) ∧
      (optCalValue ρ π_ref π_cal β r =
          β * ∑ x, ρ x * Real.log (∑ y', π_ref x y' * Real.exp (r x y' / β)) -
          ∑ x, ρ x * ∑ y, π_cal x y * r x y) ∧
      (optCalValue ρ π_ref π_cal β r =
          ∑ x, ρ x * ∑ y, π_cal x y *
            (β * Real.log (∑ y', π_ref x y' * Real.exp (r x y' / β)) - r x y)) ∧
      (optCalValue ρ π_ref π_cal β r =
          -β * ∑ x, ρ x * ∑ y, π_cal x y *
            (Real.log (gibbsPolicy π_ref r β x y) - Real.log (π_ref x y)))

open StatisticalRL.Ch7Rest.Rlhf in
/-- Restricted `eq:RLHF-policy-closed-form`, `chapters/RLHF.tex:41–59` (`eq:KL_reward` :41–45,
`π_r := argmax_π J(r, π)` :47–50, closed form :51–55, `eq:normalization` :56–59). With
`J(r, π) = E_{x∼ρ, y∼π(·|x)} r(x,y) − β E_{x∼ρ} KL(π(·|x)‖π_ref(·|x))` written out (KL with
`0 log 0 = 0`) and `π_r(y|x) = π_ref(y|x) exp(r(x,y)/β) / ∑_{y'} π_ref(y'|x) exp(r(x,y')/β)`
written out: `π_r` is a conditional policy, it maximizes `J(r, ·)` over all conditional policies,
and a conditional policy maximizes `J(r, ·)` iff it agrees with `π_r` on the support of `ρ`.

Restriction (`docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`): the printed `arg max`
treats the maximizer as unique; it is unique only on `supp ρ` (off the support any row gives the
same value), and the statement characterizes the whole argmax set instead. Also full-support
`π_ref` and finite `X`, `Y`, as in `Eq_DPO_restricted`. -/
def Eq_RLHF_policy_closed_form_restricted : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (ρ : X → ℝ) (π_ref : X → Y → ℝ) (β : ℝ),
    IsPositivePolicy π_ref → (∀ x, 0 ≤ ρ x) → 0 < β →
    ∀ r : X → Y → ℝ,
      let J : (X → Y → ℝ) → ℝ := fun π ↦
        ∑ x, ρ x * (∑ y, π x y * r x y - β * klDiv (π x) (π_ref x))
      let πr : X → Y → ℝ := fun x y ↦
        π_ref x y * Real.exp (r x y / β) / ∑ y', π_ref x y' * Real.exp (r x y' / β)
      IsCondPolicy πr ∧
      (∀ π, IsCondPolicy π → J π ≤ J πr) ∧
      ∀ π, IsCondPolicy π →
        ((∀ π', IsCondPolicy π' → J π' ≤ J π) ↔ ∀ x, 0 < ρ x → ∀ y, π x y = πr x y)

open StatisticalRL.Ch7Rest.Rlhf in
/-- Restricted prompt-shift claims of `chapters/RLHF.tex:90–98` (`eq:calibrated_value` :92–96). For
`r₁(x,y) = r₂(x,y) + c(x)`:
(a) `r₁(x,y₁) − r₁(x,y₂) = r₂(x,y₁) − r₂(x,y₂)`;
(b) `ℓ(r₁, D) = ℓ(r₂, D)` for every dataset `D` of comparisons `(x, y₊, y₋)`, with the
Bradley–Terry negative log-likelihood `ℓ(r, D) = −∑ log σ(r(x,y₊) − r(x,y₋))` (`eq:MLE`, `chapters/RLHF.tex:32–35`);
(c) `J⋆(r₁) = J⋆(r₂) + E_{x∼ρ} c(x)` for the uncalibrated `J⋆(r) = max_π J(r, π)` (:86–90) of the
KL-regularized value `eq:KL_reward` (`chapters/RLHF.tex:43–45`), written as a supremum over conditional policies;
(d) `J(r₁, π; π_cal) = J(r₂, π; π_cal)` for every conditional policy `π` (calibrated value written
out); (e) hence `J⋆(r₁; π_cal) = J⋆(r₂; π_cal)` (`eq:Jstar_calibrated`, :99–102), the supremum of the
calibrated value over conditional policies written out (this is the definition of `optCalValue`).

Hypotheses: `ρ ≥ 0`, `π_cal` a conditional policy, `β > 0`.

Restricted (`docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`): full-support `π_ref`
and finite `X`, `Y`, as in `Eq_DPO_restricted`. The printed claims hold for every `π_ref` with the
extended-real KL; the hypothesis is needed because the formal `klDiv` equals the KL divergence only
when `π_ref` has full support. Only (c) uses `π_ref` and `β` in the proof. -/
def Eq_calibrated_value_shiftInvariant_restricted : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ) (β : ℝ),
    IsPositivePolicy π_ref → (∀ x, 0 ≤ ρ x) → IsCondPolicy π_cal → 0 < β →
    ∀ (r₂ : X → Y → ℝ) (c : X → ℝ),
      let r₁ : X → Y → ℝ := fun x y ↦ r₂ x y + c x
      let nll : (X → Y → ℝ) → List (X × Y × Y) → ℝ := fun r D ↦
        -(D.map fun z ↦ Real.log (Real.sigmoid (r z.1 z.2.1 - r z.1 z.2.2))).sum
      let J : (X → Y → ℝ) → (X → Y → ℝ) → ℝ := fun r π ↦
        ∑ x, ρ x * (∑ y, π x y * r x y - β * klDiv (π x) (π_ref x))
      let Jcal : (X → Y → ℝ) → (X → Y → ℝ) → ℝ := fun r π ↦
        J r π - ∑ x, ρ x * ∑ y, π_cal x y * r x y
      (∀ (x : X) (y₁ y₂ : Y), r₁ x y₁ - r₁ x y₂ = r₂ x y₁ - r₂ x y₂) ∧
      (∀ D : List (X × Y × Y), nll r₁ D = nll r₂ D) ∧
      sSup {v | ∃ π, IsCondPolicy π ∧ J r₁ π = v} =
        sSup {v | ∃ π, IsCondPolicy π ∧ J r₂ π = v} + ∑ x, ρ x * c x ∧
      (∀ π, IsCondPolicy π → Jcal r₁ π = Jcal r₂ π) ∧
      sSup {v | ∃ π, IsCondPolicy π ∧ Jcal r₁ π = v} =
        sSup {v | ∃ π, IsCondPolicy π ∧ Jcal r₂ π = v}

end RLHFDisplays

section Thm7_6

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76

/-- Theorem 7.6 restricted (`thm:sample-complexity-plug-in-marl`, `chapters/marl.tex:384–399`;
`docs/SOURCE-ISSUES.md#C45`).

There is a universal constant `C₁ > 0` such that for every general-sum `m`-player Markov game `G`
with `S` states, horizon `H`, `A_i` actions and rewards in `[0,1]` at steps `1..H`, every `N`,
`δ ∈ (0,1)` and `0 < ε ≤ √H` with `N ≥ C₁ H³ ε⁻² log(S H N ∏_i A_i / δ)` (the printed threshold,
`N` inside the logarithm), the model-based plug-in estimator (`N` independent generative samples per
`(s, a, h)`, empirical game `empiricalGame G N hN data` with the true reward, `marl.tex:355–374`)
satisfies, under the sampling law `gameSamplingLaw`:
(a) for every causal planning oracle returning a CCE (`eq:defn-CCE`, `chapters/marl.tex:234–238`, step 1) of every empirical
game, `gap(π̂_CCE) ≤ ε` with probability at least `1 − δ`;
(b) the same for every causal oracle returning a product Nash equilibrium (`eq:defn-Nash-E`, `chapters/marl.tex:217–221`,
step-1 equality) of every empirical game, with the product-policy gap;
(c) the printed joint conclusion `gap(π̂_NE) ≤ ε ∧ gap(π̂_CCE) ≤ ε` with probability at least
`1 − δ` for any such pair of oracles.

Differences from the printed statement:
* Causal oracles (C45): the step-`h` output depends only on the rewards and kernels at steps
  `≥ h` (as for backward induction, cf. `generative_model_model_based.tex:2549`). The printed
  statement with an unspecified oracle is false (`not_thm7_6_printed`, counterexample CE2). This is a
  restriction matching the backward-induction planners named at `marl.tex:377`; no claim is made
  that it is the least restrictive repair.
* Added binders: `0 < S` and `∀ i, 0 < A_i` (the sampling law needs them) and `0 < N` (implicit
  convention, the empirical kernel needs it).
* Oracles are deterministic maps of the empirical game, and the equilibrium property is required
  for every data set (`∀ data`).
* Non-vacuity: clause (a) is non-vacuous in Lean (a causal backward-induction CCE planner,
  `causalCCEOracle_exists`). For two-player constant-sum games (`r₀ + r₁ = c` at steps `1..H`,
  e.g. `c = 1` with rewards in `[0,1]`; strict zero-sum with rewards in `[0,1]` forces zero rewards)
  clauses (b) and (c) are also non-vacuous: the product of the marginals of that planner is a causal
  exact-NE oracle (`exists_causalNEOracle_constSum`, `thm7_6_clauseB_hypotheses_constSum`). For
  general-sum games and for `m ≥ 3` players, clauses (b) and (c) are not shown non-vacuous in Lean:
  a causal NE oracle there needs Nash's existence theorem, which is not in Mathlib.
The constant proved is `C₁ = 400`. -/
def Thm7_6_restricted : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
  ∀ (m S H : ℕ) (A : Fin m → ℕ) (hS : 0 < S) (hA : ∀ i, 0 < A i) (G : MarkovGame m S H A),
    (∀ i h s a, 1 ≤ h → h ≤ H → 0 ≤ G.reward i h s a ∧ G.reward i h s a ≤ 1) →
  ∀ (N : ℕ) (hN : 0 < N) (δ ε : ℝ), 0 < δ → δ < 1 → 0 < ε → ε ≤ Real.sqrt H →
    C₁ * (H : ℝ) ^ 3 / ε ^ 2 *
        Real.log ((S : ℝ) * H * N * (∏ i, (A i : ℝ)) / δ) ≤ N →
    -- (a) CCE clause
    (∀ Occe : MarkovGame m S H A → JointPolicy m S A,
      (∀ (G₁ G₂ : MarkovGame m S H A) (h : ℕ),
        (∀ t, h ≤ t → G₁.transition t = G₂.transition t ∧ ∀ i, G₁.reward i t = G₂.reward i t) →
        Occe G₁ h = Occe G₂ h) →
      (∀ data, ∀ (s : Fin S) (i : Fin m),
        bestResponseValueJ (empiricalGame G N hN data) (Occe (empiricalGame G N hN data)) i s ≤
          valueJ (empiricalGame G N hN data) (Occe (empiricalGame G N hN data)) i 1 H s) →
      1 - δ ≤ (gameSamplingLaw G hS hA N).real
        {data | gapJ G (Occe (empiricalGame G N hN data)) ≤ ε}) ∧
    -- (b) NE clause
    (∀ One : MarkovGame m S H A → ProductPolicy m S A,
      (∀ (G₁ G₂ : MarkovGame m S H A) (h : ℕ),
        (∀ t, h ≤ t → G₁.transition t = G₂.transition t ∧ ∀ i, G₁.reward i t = G₂.reward i t) →
        ∀ i, One G₁ i h = One G₂ i h) →
      (∀ data, ∀ (s : Fin S) (i : Fin m),
        value (empiricalGame G N hN data) (One (empiricalGame G N hN data)) i 1 H s =
          bestResponseValue (empiricalGame G N hN data) (One (empiricalGame G N hN data)) i s) →
      1 - δ ≤ (gameSamplingLaw G hS hA N).real
        {data | gap G (One (empiricalGame G N hN data)) ≤ ε}) ∧
    -- (c) joint clause (the printed conclusion)
    (∀ (One : MarkovGame m S H A → ProductPolicy m S A)
        (Occe : MarkovGame m S H A → JointPolicy m S A),
      (∀ (G₁ G₂ : MarkovGame m S H A) (h : ℕ),
        (∀ t, h ≤ t → G₁.transition t = G₂.transition t ∧ ∀ i, G₁.reward i t = G₂.reward i t) →
        ∀ i, One G₁ i h = One G₂ i h) →
      (∀ (G₁ G₂ : MarkovGame m S H A) (h : ℕ),
        (∀ t, h ≤ t → G₁.transition t = G₂.transition t ∧ ∀ i, G₁.reward i t = G₂.reward i t) →
        Occe G₁ h = Occe G₂ h) →
      (∀ data, ∀ (s : Fin S) (i : Fin m),
        value (empiricalGame G N hN data) (One (empiricalGame G N hN data)) i 1 H s =
          bestResponseValue (empiricalGame G N hN data) (One (empiricalGame G N hN data)) i s) →
      (∀ data, ∀ (s : Fin S) (i : Fin m),
        bestResponseValueJ (empiricalGame G N hN data) (Occe (empiricalGame G N hN data)) i s ≤
          valueJ (empiricalGame G N hN data) (Occe (empiricalGame G N hN data)) i 1 H s) →
      1 - δ ≤ (gameSamplingLaw G hS hA N).real
        {data | gap G (One (empiricalGame G N hN data)) ≤ ε ∧
          gapJ G (Occe (empiricalGame G N hN data)) ≤ ε})

end Thm7_6

section Thm7_7

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.AdaptiveKL

/-- Theorem 7.7 restricted (`thm:Q-FTRL`, `chapters/marl.tex:441–467`; `docs/SOURCE-ISSUES.md#C39`).

Restricted variant: proves the existential sample-complexity guarantee with an explicit
reconstructed witness algorithm; the witness is not shown to be Q-FTRL and is not model-based
(it builds no empirical transition kernel).

There is a universal constant `C > 0` such that:
(b) for all `m`, `S ≥ 1`, `H`, action counts `A_i ≥ 1`, `δ ∈ (0,1)`, `0 < ε ≤ H` and every known
reward table `r` with `r_{i,h} ∈ [0,1]` at steps `1..H`, there is an algorithm in the adaptive
generative model (`marl.tex:307–311`): a query rule choosing each `(h, s, a)` from a finite
distribution depending on all previous queries and answers, `N` queries in total, and an output
joint (possibly correlated) Markov policy computed from the history, with
`N ≤ C H⁴ S (Σ_i A_i) ε⁻² log(4 H S Σ_i A_i / δ)`, such that for every transition kernel `P`, with
probability at least `1 − δ`, `gap(π̂_CCE) ≤ ε` (`eq:defn-NE-gap`, `chapters/marl.tex:328–343`, applied to the joint output);
(a) for two players with `S ≥ 1`, `A₁, A₂ ≥ 1`, `δ ∈ (0,1)`, `0 < ε ≤ H` and every known zero-sum
reward (`r₁ ∈ [0,1]`, `r₂ = −r₁` at steps `1..H`, `marl.tex:50–54`), there is such an algorithm
outputting a *product* policy, with `N ≤ C H⁴ S A ε⁻² log(8 H S A / δ)`, `A := max(A₁, A₂)`, and
`gap(π̂_NE) ≤ ε` with probability at least `1 − δ`.

Readings and disclosures:
* Restriction (C39): the printed claim is that "a model-based algorithm (i.e., Q-FTRL)" attains the
  rates. Q-FTRL is not defined in the monograph (`marl.tex:432`). The witness here is a
  reconstructed algorithm (optimistic Hedge with backward induction and per-agent generative queries
  `(h, s, (b, a_{-i}))`, `a_{-i}` drawn from the other players' current Hedge weights); it is not
  shown to be Q-FTRL, and it is not model-based in the sense of :355–377 (it builds no empirical
  transition kernel); "model-based" is not formalized. Whether Q-FTRL itself attains the rate is
  not checked.
* `A` is undefined in the source (C39); the `max` reading is proved, which implies the `A₁ + A₂`
  and `A₁ = A₂ = A` readings.
* `Õ` is read as a universal constant times `log(4HSΣ_iA_i/δ)` (resp. `log(8HSA/δ)`), with no
  dependence on `ε` in the logarithm; the bound holds uniformly over `ε ∈ (0, H]` (`marl.tex:476`).
  The query count `N` is deterministic.
* The algorithm may depend on the known reward table (`generative_model_model_based.tex:31`; the
  sampler returns only `s′`), on `δ` and on `ε`, but not on `P`.
* The two clauses are stated with separate existentials (one algorithm per clause, sharing `C`).
  A single algorithm serving both is obtained by branching on the known reward table, taking
  `N = 0` on the overlap of the two classes (two players with `r ≡ 0` on steps `1..H`), where every
  policy has gap `0` (argued in prose; not machine-checked).
* Added binders `S ≥ 1`, `A_i ≥ 1` (source convention `𝒮 = {1..S}`, `𝒜_i = {1..A_i}`; in Lean an
  empty action or state type admits no policy or no query rule). Rewards are constrained only at
  steps `1..H`, the only steps the values read. -/
def Thm7_7_restricted : Prop :=
  ∃ C : ℝ, 0 < C ∧
  (∀ (m S H : ℕ) (A : Fin m → ℕ), 1 ≤ S → (∀ i, 1 ≤ A i) →
    ∀ δ ε : ℝ, 0 < δ → δ < 1 → 0 < ε → ε ≤ H →
    ∀ rew : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ,
      (∀ i h s a, 1 ≤ h → h ≤ H → 0 ≤ rew i h s a ∧ rew i h s a ≤ 1) →
    ∃ (N : ℕ)
      (rule : (t : ℕ) → (Fin t → Query m S H A × Fin S) → FiniteDistribution (Query m S H A))
      (out : (Fin N → Query m S H A × Fin S) → JointPolicy m S A),
      (N : ℝ) ≤ C * (H : ℝ) ^ 4 * S * (∑ i, (A i : ℝ)) / ε ^ 2 *
          Real.log (4 * H * S * (∑ i, (A i : ℝ)) / δ) ∧
      ∀ P : ℕ → Fin S → ((i : Fin m) → Fin (A i)) → FiniteDistribution (Fin S),
        1 - δ ≤ ∑ hist, (interactionLaw rule (genEnv (⟨P, rew⟩ : MarkovGame m S H A)) N).prob hist *
          (if gapJ (⟨P, rew⟩ : MarkovGame m S H A) (out hist) ≤ ε then 1 else 0)) ∧
  (∀ (S H : ℕ) (A : Fin 2 → ℕ), 1 ≤ S → (∀ i, 1 ≤ A i) →
    ∀ δ ε : ℝ, 0 < δ → δ < 1 → 0 < ε → ε ≤ H →
    ∀ rew : Fin 2 → ℕ → Fin S → ((i : Fin 2) → Fin (A i)) → ℝ,
      (∀ h s a, 1 ≤ h → h ≤ H →
        0 ≤ rew 0 h s a ∧ rew 0 h s a ≤ 1 ∧ rew 1 h s a = - rew 0 h s a) →
    ∃ (N : ℕ)
      (rule : (t : ℕ) → (Fin t → Query 2 S H A × Fin S) → FiniteDistribution (Query 2 S H A))
      (out : (Fin N → Query 2 S H A × Fin S) → ProductPolicy 2 S A),
      (N : ℝ) ≤ C * (H : ℝ) ^ 4 * S * ((max (A 0) (A 1) : ℕ) : ℝ) / ε ^ 2 *
          Real.log (8 * H * S * ((max (A 0) (A 1) : ℕ) : ℝ) / δ) ∧
      ∀ P : ℕ → Fin S → ((i : Fin 2) → Fin (A i)) → FiniteDistribution (Fin S),
        1 - δ ≤ ∑ hist, (interactionLaw rule (genEnv (⟨P, rew⟩ : MarkovGame 2 S H A)) N).prob hist *
          (if gap (⟨P, rew⟩ : MarkovGame 2 S H A) (out hist) ≤ ε then 1 else 0))

end Thm7_7

section Eq_mdp_value_Q_restricted
universe v

open StatisticalRL StatisticalRL.RobustRL.Ch7 in
/-- Unnumbered display `eq:mdp-value-Q`, `chapters/robust_RL.tex:88–98` ("there exists at least
one deterministic policy that maximizes the robust value function (resp. robust Q-function)
simultaneously across all states (resp. state-action pairs)"). This is a displayed claim; it
adds no numbered-ledger entry.

Objects: RMDP `{S, A, γ, U^σ(P^0), r}` with finite `S`, `A`, reward in `[0,1]`, `0 ≤ γ < 1`
(`:24–28`; a `DiscountedMDP` whose `transition` is the nominal kernel `P^0`); the
`(s,a)`-rectangular set `U^σ(P^0)` of complete kernels whose rows lie in `ball(P^0_{s,a}, σ)`,
`σ > 0` (`:31–52`), where `ball` is the TV ball (half-L1 distance, `tvBall`), the support-aware
χ² ball (`chiBall`), or any other row-set family in which every linear functional
`q ↦ ⟨q, V⟩` attains its infimum on every nominal row's set; `V^{π,σ}(s) = inf_P V^{π,P}(s)` and
`Q^{π,σ}(s,a) = inf_P Q^{π,P}(s,a)` (`:76–84`), where `V^{π,P}`, `Q^{π,P}` are the actual
infinite-trajectory value and forced-first-action Q-value in the MDP with kernel `P`
(static adversary: one kernel for the whole trajectory, `:78`). The policy class of `max_π` is
the book's class of stationary randomized policies `π : S → Δ(A)` (`prelim.tex:66`).

For each such ball family separately: there is a single deterministic `f : S → A` whose policy
`s ↦ δ_{f(s)}` dominates every stationary randomized policy in robust value at every state and
in robust Q-value at every state-action pair. Since `detPolicy f` is itself such a policy, this
is `V^{π⋆,σ}(s) = max_π V^{π,σ}(s)` and `Q^{π⋆,σ}(s,a) = max_π Q^{π,σ}(s,a)` with the maxima
attained.

Restricted (scope disclosure, `docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`): the
source builds `U^σ` from an unspecified "distance-like metric" ρ (`:36–46`) and names TV and χ²
as the instances it studies (`:52`). The entry covers TV, χ² and every row-set family with
attained row infima; reading "distance-like" as implying attainment is an interpretation, and
families without attainment are not claimed. Further disclosures: (a) one `f` serves both the
value and the Q clause, whereas the source's "resp." would allow separate policies;
(b) `DiscountedMDP` allows `γ = 0`; (c) for TV and χ² the proof needs only `σ ≥ 0`. The statement
concerns stationary randomized policies and the book's static adversary only; history-dependent
policies (and dynamic adversaries) are not claimed. -/
def Eq_mdp_value_Q_restricted : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (σ : ℝ), 0 < σ →
    ∀ ball : RowBall State, (ball = tvBall ∨ ball = chiBall ∨
      ∀ (s : State) (a : Action) (V : State → ℝ), ∃ q ∈ ball (M.transition s a) σ,
        ∀ q' ∈ ball (M.transition s a) σ, ∑ x, q.prob x * V x ≤ ∑ x, q'.prob x * V x) →
    ∃ f : State → Action,
      (∀ (π : StationaryPolicy State Action) (s : State),
        robustPolicyValue ball M σ π s ≤ robustPolicyValue ball M σ (detPolicy f) s) ∧
      (∀ (π : StationaryPolicy State Action) (s : State) (a : Action),
        robustPolicyQ ball M σ π s a ≤ robustPolicyQ ball M σ (detPolicy f) s a)

end Eq_mdp_value_Q_restricted

section RobustBellman
universe v

open StatisticalRL StatisticalRL.RobustRL.Ch7 in
/-- `eq:bellman-equ-infinite-all` (`eq:bellman-equ-pi-infinite`, `eq:bellman-equ-star-infinite`),
`chapters/robust_RL.tex:102–113`, with the robust objects of `:71–84` and `V^{⋆,σ}`, `Q^{⋆,σ}` of
`eq:mdp-value-Q` (`:88–98`).

Objects as in `Eq_mdp_value_Q_restricted`: a `DiscountedMDP` whose `transition` is the nominal
kernel `P^0`, the TV ball (half-L1 distance, `tvBall`), the support-aware χ² ball (`chiBall`) or
any row-set family with attained row infima, radius `σ > 0`, `V^{π,σ}` / `Q^{π,σ}` the infimum over `(s,a)`-rectangular admissible kernels of the actual
infinite-trajectory value / forced-first-action Q-value (static adversary), and `⟨P, V⟩ =
∑_{s'} P(s') V(s')`. For each such ball family:
(1) robust Bellman consistency `Q^{π,σ}(s,a) = r(s,a) + γ inf_{P ∈ U^σ(P^0_{s,a})} ⟨P, V^{π,σ}⟩`
for every stationary randomized policy `π` ("π stands for any policy", `:113`);
(2) robust Bellman optimality with `Q^{⋆,σ}(s,a) = max_π Q^{π,σ}(s,a)` and
`V^{⋆,σ}(s) = max_π V^{π,σ}(s)` (`:95–96`; written as suprema over stationary randomized
policies, `robustOptimalValue`);
(3) for every stationary policy `π⋆` maximizing the robust value at every state (`:90–92`),
`V^{π⋆,σ} = V^{⋆,σ}` and `Q^{π⋆,σ} = Q^{⋆,σ}`, so (2) is also the display with
`Q^{⋆,σ} := Q^{π⋆,σ}`, `V^{⋆,σ} := V^{π⋆,σ}`.

Restricted (scope disclosure, `docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`): the
source states these displays for a general `(s,a)`-rectangular set built from a 'distance-like
metric' ρ (`:36–46`) and names TV and χ² as its instances (`:52`). The entry covers TV, χ² and
every row-set family whose row infima of linear functionals are attained; reading
"distance-like" as implying attainment is an interpretation, and families without attainment are
not claimed. As in `Eq_mdp_value_Q_restricted`, 'any policy' is read as the book's stationary
randomized policies (`prelim.tex:65`); history-dependent policies and dynamic adversaries are not
claimed. Stronger than printed in two harmless ways: `π⋆` may be any (not necessarily
deterministic) value-maximizing stationary policy, and for TV and χ² the library needs only
`σ ≥ 0`. -/
def Eq_bellman_equ_infinite_all_restricted : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (σ : ℝ), 0 < σ →
    ∀ ball : RowBall State, (ball = tvBall ∨ ball = chiBall ∨
      ∀ (s : State) (a : Action) (V : State → ℝ), ∃ q ∈ ball (M.transition s a) σ,
        ∀ q' ∈ ball (M.transition s a) σ, ∑ x, q.prob x * V x ≤ ∑ x, q'.prob x * V x) →
      (∀ (π : StationaryPolicy State Action) (s : State) (a : Action),
        robustPolicyQ ball M σ π s a = M.reward s a + M.discount *
          ⨅ q : ball (M.transition s a) σ,
            ∑ s', q.1.prob s' * robustPolicyValue ball M σ π s') ∧
      (∀ (s : State) (a : Action),
        sSup (Set.range fun π : StationaryPolicy State Action ↦ robustPolicyQ ball M σ π s a) =
          M.reward s a + M.discount *
            ⨅ q : ball (M.transition s a) σ,
              ∑ s', q.1.prob s' * robustOptimalValue ball M σ s') ∧
      (∀ πs : StationaryPolicy State Action,
        (∀ (π : StationaryPolicy State Action) (s : State),
          robustPolicyValue ball M σ π s ≤ robustPolicyValue ball M σ πs s) →
        (∀ s : State, robustPolicyValue ball M σ πs s = robustOptimalValue ball M σ s) ∧
        ∀ (s : State) (a : Action), robustPolicyQ ball M σ πs s a =
          sSup (Set.range fun π : StationaryPolicy State Action ↦ robustPolicyQ ball M σ π s a))

open StatisticalRL StatisticalRL.RobustRL.Ch7 in
/-- Unnumbered claims on the robust Bellman operator `eq:robust_bellman` and DRVI,
`chapters/robust_RL.tex:114–133` ("`Q^{⋆,σ}` is the unique fixed point of `T^σ`", "`γ`-contraction
… w.r.t. the `ℓ_∞` norm", DRVI from an arbitrary initialization "converges geometrically fast")
and `:261–262` (the DRVI iterates `Q̂_t`, `Q̂_0 = 0` (`:268`), "converge linearly to the unique fixed
point `Q̂^{⋆,σ}`" of the empirical operator).

Objects as in `Eq_bellman_equ_infinite_all_restricted`. The operator is written out:
`T^σ(Q)(s,a) = r(s,a) + γ inf_{P ∈ U^σ(P^0_{s,a})} ⟨P, V⟩`, `V(s) = max_b Q(s,b)` (`:118–127`).
`Q^{⋆,σ} := Q^{π⋆,σ}` for an arbitrary stationary policy `π⋆` maximizing the robust value at every
state (`eq:mdp-value-Q`, `chapters/robust_RL.tex:93–98`; such a deterministic `π⋆` exists by `Eq_mdp_value_Q_restricted`). For each such ball family:
(a) `T^σ Q^{⋆,σ} = Q^{⋆,σ}`; (b) every fixed point of `T^σ` equals `Q^{⋆,σ}`; (c) `T^σ` is a
`γ`-contraction in the sup norm on `ℝ^{S×A}`; (d) from any initialization `Q₀`,
`‖(T^σ)^t Q₀ − Q^{⋆,σ}‖_∞ ≤ γ^t ‖Q₀ − Q^{⋆,σ}‖_∞`; (e) the DRVI iterates from `0` satisfy
`|Q_t(s,a) − Q^{⋆,σ}(s,a)| ≤ γ^t/(1−γ)`. The nominal kernel is arbitrary, so the statement
applied to the empirical model `P̂^0` is the `:261` claim for `T̂^σ` and `Q̂^{⋆,σ}`.

Restricted (scope disclosure, `docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`): the
source states this operator and DRVI claim for a general `(s,a)`-rectangular set built from a
'distance-like metric' ρ (`:36–46`) and names TV and χ² as its instances (`:52`). The entry covers
TV, χ² and every row-set family with attained row infima; reading "distance-like" as implying
attainment is an interpretation, and families without attainment are not claimed. As in
`Eq_mdp_value_Q_restricted`, 'any policy' is read as the book's stationary randomized policies
(`prelim.tex:65`); history-dependent policies and dynamic adversaries are not claimed. As in
`Eq_bellman_equ_infinite_all_restricted`, `π⋆` may be randomized, and for TV and χ² `σ ≥ 0`
suffices. -/
def Eq_robust_bellman_fixedPoint_restricted : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (σ : ℝ), 0 < σ →
    ∀ ball : RowBall State, (ball = tvBall ∨ ball = chiBall ∨
      ∀ (s : State) (a : Action) (V : State → ℝ), ∃ q ∈ ball (M.transition s a) σ,
        ∀ q' ∈ ball (M.transition s a) σ, ∑ x, q.prob x * V x ≤ ∑ x, q'.prob x * V x) →
    ∀ πs : StationaryPolicy State Action,
      (∀ (π : StationaryPolicy State Action) (s : State),
        robustPolicyValue ball M σ π s ≤ robustPolicyValue ball M σ πs s) →
      let T : (State → Action → ℝ) → State → Action → ℝ := fun Q s a ↦
        M.reward s a + M.discount *
          ⨅ q : ball (M.transition s a) σ, ∑ s', q.1.prob s' * ⨆ b, Q s' b
      let Qs : State → Action → ℝ := robustPolicyQ ball M σ πs
      T Qs = Qs ∧
      (∀ Q : State → Action → ℝ, T Q = Q → Q = Qs) ∧
      (∀ Q Q' : State → Action → ℝ, ‖T Q - T Q'‖ ≤ M.discount * ‖Q - Q'‖) ∧
      (∀ (Q₀ : State → Action → ℝ) (t : ℕ),
        ‖T^[t] Q₀ - Qs‖ ≤ M.discount ^ t * ‖Q₀ - Qs‖) ∧
      (∀ (t : ℕ) (s : State) (a : Action),
        |T^[t] 0 s a - Qs s a| ≤ M.discount ^ t / (1 - M.discount))

end RobustBellman

section MarlEquilibria

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76

/-- Best responses and Bellman optimality for agent `i` (`eq:defn-optimal-V` and the prose after
it), `chapters/marl.tex:119–143` (definition :119–126, existence of a best response attaining
`V^{⋆,π_{-i}}_{i,h}(s)` at all `(s, h)` simultaneously :128–132, Bellman optimality with terminal
value `0` :135–143). Markov policies :71–91, values `eq:value-function-defn` :96–106.

For a joint Markov policy `π` and an agent `i` with `A i ≥ 1` actions (`Δ(A_i)` nonempty),
`V⋆_h(s) := ⨆_{π'} V^{π'_i × π_{-i}}_{i,h}(s)` is the supremum over all Markov policies `π'` of
agent `i` of the value `valueJ … i h (H + 1 - h) s` (steps `h, …, H`) of `deviate π i π'`, i.e.
`π'_i` played independently of the marginal `π_{-i}` of `π`. Proved: (1) the supremum dominates every
deviation (it is a genuine maximum, not a junk `iSup`); (2) one Markov policy `μ` attains it at
every `h ∈ [1, H]` and every `s`; (3) `V⋆_{H+1} = 0`; (4) the Bellman optimality equation for
`h ∈ [1, H]`:
`V⋆_h(s) = max_b E_{a ∼ π_h(·|s)}[r_{i,h}(s, a[i ↦ b]) + ⟨P_h(·|s, a[i ↦ b]), V⋆_{h+1}⟩]`;
the expectation over `a ∼ π_h(·|s)` with `a_i` replaced by `b` is the printed expectation over
`a_{-i} ∼ π_{-i,h}(·|s)`. -/
def Marl_bestResponse_exists : Prop :=
  ∀ (m S H : ℕ) (A : Fin m → ℕ) (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m),
    0 < A i →
    let Vstar : ℕ → Fin S → ℝ := fun h s =>
      ⨆ π' : PlayerPolicy S (A i), valueJ G (deviate π i π') i h (H + 1 - h) s
    (∀ (π' : PlayerPolicy S (A i)) (h : ℕ), 1 ≤ h → h ≤ H → ∀ s : Fin S,
        valueJ G (deviate π i π') i h (H + 1 - h) s ≤ Vstar h s) ∧
    (∃ μ : PlayerPolicy S (A i), ∀ h : ℕ, 1 ≤ h → h ≤ H → ∀ s : Fin S,
        valueJ G (deviate π i μ) i h (H + 1 - h) s = Vstar h s) ∧
    (∀ s : Fin S, Vstar (H + 1) s = 0) ∧
    (∀ h : ℕ, 1 ≤ h → h ≤ H → ∀ s : Fin S,
        Vstar h s = ⨆ b : Fin (A i), ∑ a' : (j : Fin m) → Fin (A j), (π h s).prob a' *
          (G.reward i h s (Function.update a' i b) +
            (G.transition h s (Function.update a' i b)).expectation (Vstar (h + 1))))

/-- Every Nash equilibrium is a CCE, and the converse fails (`chapters/marl.tex:232–240`: CCE
`eq:defn-CCE` :232–238 and the claim at :240; NE `eq:defn-Nash-E` :213–221, product policies
:88–91).

(1) If `σ` is an NE (`IsNE`, `eq:defn-Nash-E`) and the joint policy `π` has the product law
`π_h(a|s) = ∏_j σ_{j,h}(a_j|s)` at every `(h, s)`, then `π` is a CCE (`IsCCE`, `eq:defn-CCE`).
(2) There is a two-player, one-state, one-step game with rewards in `[0,1]` (the coordination game:
reward `1` to both players when their two actions agree) and a CCE `π` (uniform on `{(0,0),(1,1)}`)
whose step-1 law is not the product law of any product policy. Since NE is defined only for product
policies (:213–214), such a `π` is not an NE. For product policies CCE and NE coincide (library
`StatisticalRL.Ch7Rest.Marl76.isNE_iff_isCCE_toJoint`), so for a CCE "not an NE" amounts to
"not a product". -/
def Marl_NE_isCCE_not_converse : Prop :=
  (∀ (m S H : ℕ) (A : Fin m → ℕ) (G : MarkovGame m S H A) (σ : ProductPolicy m S A)
      (π : JointPolicy m S A),
      (∀ (h : ℕ) (s : Fin S) (a : (j : Fin m) → Fin (A j)), (π h s).prob a = jointProb σ h s a) →
      IsNE G σ → IsCCE G π) ∧
  ∃ (G : MarkovGame 2 1 1 (fun _ => 2)) (π : JointPolicy 2 1 (fun _ => 2)),
    (∀ (i : Fin 2) (h : ℕ) (s : Fin 1) (a : (j : Fin 2) → Fin ((fun _ : Fin 2 => 2) j)),
      0 ≤ G.reward i h s a ∧ G.reward i h s a ≤ 1) ∧
    IsCCE G π ∧
    ∀ σ : ProductPolicy 2 1 (fun _ => 2),
      ¬ ∀ a : (j : Fin 2) → Fin ((fun _ : Fin 2 => 2) j), (π 1 0).prob a = jointProb σ 1 0 a

end MarlEquilibria

section ConvexDistanceTV

open MeasureTheory

/-- `d_cvx(P, Q) ≤ TV(P, Q)`, `chapters/inference.tex:129`, with `d_cvx` from
`eqn:convex-distance` (:124–127, supremum of `|P(A) − Q(A)|` over all convex `A ⊆ ℝ^d`) and TV from
`eq:TV` (`chapters/intro.tex:218–227`, supremum over the σ-algebra). Laws are probability measures
on `ℝ^d = Fin d → ℝ` with its Borel σ-algebra. Reading: a convex set need not be Borel (an open disc
plus any subset of its boundary circle), so `P(A)` for convex `A` is the outer measure `P.real A`,
the same reading as the library definition
`StatisticalRL.Ch7Rest.TDInference.Thm7_11_printed_allConvex` in
`Formalization/Ch7Rest/TDInferencePrinted711.lean` (a library definition, not a statement entry). Both suprema are of sets bounded by `1` and
containing `|P(∅) − Q(∅)|`, so `sSup` is the genuine supremum. -/
def Eq_convex_distance_le_TV : Prop :=
  ∀ (d : ℕ) (P Q : Measure (Fin d → ℝ)), IsProbabilityMeasure P → IsProbabilityMeasure Q →
    sSup {x : ℝ | ∃ C : Set (Fin d → ℝ), Convex ℝ C ∧ x = |P.real C - Q.real C|} ≤
      sSup {x : ℝ | ∃ A : Set (Fin d → ℝ), MeasurableSet A ∧ x = |P.real A - Q.real A|}

end ConvexDistanceTV

section TDWeights

/-- The plug-in weights `w_{t,T} := t / ∑_{u=1}^T u = 2t / (T(T+1))`,
`chapters/inference.tex:173–177` (the display at :175), and they sum to `1` (implicit in their use
as weights in `Γ̂_T`, :168). The index is 0-based: `t : Fin T` is the source's `t + 1`. -/
def Eq_tdWeights_sum : Prop :=
  ∀ T : ℕ, 1 ≤ T →
    (∀ t : Fin T, ((t : ℝ) + 1) / ∑ u : Fin T, ((u : ℝ) + 1) =
      2 * ((t : ℝ) + 1) / ((T : ℝ) * (T + 1))) ∧
    ∑ t : Fin T, ((t : ℝ) + 1) / ∑ u : Fin T, ((u : ℝ) + 1) = 1

end TDWeights

end StatisticalRL.Statements.Ch7
