import Formalization.Ch7Rest.Marl78Defs

/-!
# Corrected Theorem 7.8: statement (definitions only, no proofs)
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl

open StatisticalRL AdaptiveKL

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
  ∃ (Θ : Type) (G : Θ → MarkovGame m S H A),
    (∀ θ, zeroSumAdm (G θ)) ∧ (∀ θ θ', (G θ).reward = (G θ').reward) ∧
    ∀ N : ℕ, (N : ℝ) < c₂ * (H : ℝ) ^ 4 * S * ((Finset.univ.sup A : ℕ) : ℝ) / ε ^ 2 →
    ∀ (Ω : Type) (μ : Ω → ℝ), (∀ ω, 0 ≤ μ ω) → HasSum μ 1 →
    ∀ (rule : Ω → (t : ℕ) → (Fin t → Query m S H A × Fin S) →
        FiniteDistribution (Query m S H A))
      (out : Ω → (Fin N → Query m S H A × Fin S) → JointPolicy m S A),
    ∃ θ, (1 : ℝ) / 4 ≤ ∑' ω, μ ω *
      ∑ hist, (interactionLaw (rule ω) (genEnv (G θ)) N).prob hist *
        (if ε < gapJ (G θ) (out ω hist) then 1 else 0)

/-- Theorem 7.8 corrected, normalised constant-sum variant (`thm:lower-marl`,
`chapters/marl.tex:487–503`; `docs/SOURCE-ISSUES.md#C40`). Identical to `Thm7_8_corrected` except that the
games satisfy `constSumAdm` (rewards sum to `1` over the players, every reward in `[0,1]`, i.e. the
reward normalisation of `marl.tex:41–43` with the constant shift allowed by the footnote at :53)
instead of `zeroSumAdm`. -/
def Thm7_8_corrected_constSum : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
  ∀ (m S H : ℕ) (A : Fin m → ℕ), 2 ≤ m → 2 ≤ S → 2 ≤ H → 2 ≤ Finset.univ.sup A →
  ∀ ε : ℝ, 0 < ε → ε ≤ c₁ * H →
  ∃ (Θ : Type) (G : Θ → MarkovGame m S H A),
    (∀ θ, constSumAdm (G θ)) ∧ (∀ θ θ', (G θ).reward = (G θ').reward) ∧
    ∀ N : ℕ, (N : ℝ) < c₂ * (H : ℝ) ^ 4 * S * ((Finset.univ.sup A : ℕ) : ℝ) / ε ^ 2 →
    ∀ (Ω : Type) (μ : Ω → ℝ), (∀ ω, 0 ≤ μ ω) → HasSum μ 1 →
    ∀ (rule : Ω → (t : ℕ) → (Fin t → Query m S H A × Fin S) →
        FiniteDistribution (Query m S H A))
      (out : Ω → (Fin N → Query m S H A × Fin S) → JointPolicy m S A),
    ∃ θ, (1 : ℝ) / 4 ≤ ∑' ω, μ ω *
      ∑ hist, (interactionLaw (rule ω) (genEnv (G θ)) N).prob hist *
        (if ε < gapJ (G θ) (out ω hist) then 1 else 0)

end StatisticalRL.Ch7Rest.Marl
