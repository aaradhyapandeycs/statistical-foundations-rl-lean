import Formalization.RobustRL.TVWeakDefinitions
import Formalization.ModelFree.QLearningRobustDefinitions
import Formalization.Ch7Rest.FedGeneric710
import Formalization.RobustRL.Ch7.Ch7Definitions
import Formalization.Ch7Rest.Marl78Defs

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

end StatisticalRL.Statements.Ch7
