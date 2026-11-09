import Formalization.RobustRL.TVWeakDefinitions
import Formalization.ModelFree.QLearningRobustDefinitions
import Formalization.Ch7Rest.FedGeneric710
import Formalization.RobustRL.Ch7.Ch7Definitions
import Formalization.Ch7Rest.Marl78Defs
import Formalization.Ch7Rest.VPODefs712
import Formalization.Ch7Rest.Marl76Defs

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
/-- Theorem 7.10, `thm:lower_bound`, `chapters/federated_RL.tex:227–239` (generic algorithm
`alg:general_fed_alg_with_inter_comm`, lines 166–220, box 200–220), read with the universal
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
`Q_0 = 0` line 207, return line 219). Disclosure: only exact averaging is modelled; the sentence
at line 196 allowing any distributed mean-estimation routine (including compressed variants) is
not covered. The expectation is over the genuine independent generative sampling law
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
def Thm7_10 : Prop :=
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
rows at `(s₀, a₀)` and `(s₀, a₁)`. -/
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
two models of the proof differ only in the nominal rows at `(s₀, a₀)` and `(s₀, a₁)`. -/
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
`T ≥ c₁ log(N/(1−γ))/(1−γ)` instead of `T = c₁ log(N/(1−γ))` (`:438`). This is a minimal edit
of the printed formula; tightness of the log factor is not shown.

For universal constants `c₁, c₂ > 0` (proved with `c₁ = 2`, `c₂ = 10⁶`), every finite `S`, `A`,
every RMDP with `σ > 0`, `γ ∈ [1/4, 1)`, `δ ∈ (0,1)`, `ε ∈ (0, 1/(1−γ)]`, `N > 0` with
`N ≥ c₂ (1 + max{√σ,σ}/(1−γ)) log(SAN/δ) / ((1−γ)³ ε²)`, every such `T` and every greedy
selector `π̂` of `Q̂_T`: with probability at least `1−δ`, `V^{⋆,σ}(s) − V^{π̂,σ}(s) ≤ ε` for all
`s`. The oracle-planner Remark (`:453–457`) is indexed separately as `Remark7_2_restricted`. Not
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
(a) for every causal planning oracle returning a CCE (`eq:defn-CCE`, step 1) of every empirical
game, `gap(π̂_CCE) ≤ ε` with probability at least `1 − δ`;
(b) the same for every causal oracle returning a product Nash equilibrium (`eq:defn-Nash-E`,
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
* Non-vacuity: clause (a) is non-vacuous in Lean (a causal backward-induction CCE planner is
  constructed, `causalCCEOracle_exists`). Clauses (b) and (c) are not shown non-vacuous in Lean:
  a causal NE oracle for general-sum games needs Nash's existence theorem, which is not in Mathlib.
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
probability at least `1 − δ`, `gap(π̂_CCE) ≤ ε` (`eq:defn-NE-gap`, applied to the joint output);
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

section Eq_mdp_value_Q
universe v

open StatisticalRL StatisticalRL.RobustRL.Ch7 in
/-- Unnumbered display `eq:mdp-value-Q`, `chapters/robust_RL.tex:88–98` ("there exists at least
one deterministic policy that maximizes the robust value function (resp. robust Q-function)
simultaneously across all states (resp. state-action pairs)"). This is a displayed claim; it
adds no numbered-ledger entry.

Objects: RMDP `{S, A, γ, U^σ(P^0), r}` with finite `S`, `A`, reward in `[0,1]`, `0 ≤ γ < 1`
(`:24–28`; a `DiscountedMDP` whose `transition` is the nominal kernel `P^0`); the
`(s,a)`-rectangular set `U^σ(P^0)` of complete kernels whose rows lie in the TV ball
(half-L1 distance, `tvBall`) or the support-aware χ² ball (`chiBall`) of radius `σ > 0`
around the nominal rows (`:31–52`); `V^{π,σ}(s) = inf_P V^{π,P}(s)` and
`Q^{π,σ}(s,a) = inf_P Q^{π,P}(s,a)` (`:76–84`), where `V^{π,P}`, `Q^{π,P}` are the actual
infinite-trajectory value and forced-first-action Q-value in the MDP with kernel `P`
(static adversary: one kernel for the whole trajectory, `:78`). The policy class of `max_π` is
the book's class of stationary randomized policies `π : S → Δ(A)` (`prelim.tex:66`).

For each of the two balls separately: there is a single deterministic `f : S → A` whose policy
`s ↦ δ_{f(s)}` dominates every stationary randomized policy in robust value at every state and
in robust Q-value at every state-action pair. Since `detPolicy f` is itself such a policy, this
is `V^{π⋆,σ}(s) = max_π V^{π,σ}(s)` and `Q^{π⋆,σ}(s,a) = max_π Q^{π,σ}(s,a)` with the maxima
attained.

Disclosures (none is a source issue): (a) one `f` serves both the value and the Q clause,
whereas the source's "resp." would allow separate policies; (b) `DiscountedMDP` allows `γ = 0`;
(c) the proof needs only `σ ≥ 0`. The statement concerns stationary randomized policies and the
book's static adversary only; history-dependent policies (and dynamic adversaries) are not
claimed. -/
def Eq_mdp_value_Q : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (σ : ℝ), 0 < σ →
    (∃ f : State → Action,
      (∀ (π : StationaryPolicy State Action) (s : State),
        robustPolicyValue tvBall M σ π s ≤ robustPolicyValue tvBall M σ (detPolicy f) s) ∧
      (∀ (π : StationaryPolicy State Action) (s : State) (a : Action),
        robustPolicyQ tvBall M σ π s a ≤ robustPolicyQ tvBall M σ (detPolicy f) s a)) ∧
    (∃ f : State → Action,
      (∀ (π : StationaryPolicy State Action) (s : State),
        robustPolicyValue chiBall M σ π s ≤ robustPolicyValue chiBall M σ (detPolicy f) s) ∧
      (∀ (π : StationaryPolicy State Action) (s : State) (a : Action),
        robustPolicyQ chiBall M σ π s a ≤ robustPolicyQ chiBall M σ (detPolicy f) s a))

end Eq_mdp_value_Q

end StatisticalRL.Statements.Ch7
