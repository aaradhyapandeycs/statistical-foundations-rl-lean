import Formalization.RobustRL.TVWeakDefinitions
import Formalization.ModelFree.QLearningRobustDefinitions

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

end StatisticalRL.Statements.Ch7
