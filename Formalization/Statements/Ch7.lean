import Formalization.RobustRL.TVWeakDefinitions
import Formalization.ModelFree.QLearningRobustDefinitions
import Formalization.Ch7Rest.FedGeneric710

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

end StatisticalRL.Statements.Ch7
