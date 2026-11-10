import Formalization.MultiAgent.LowerBound.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Theorem 7.7 (`thm:Q-FTRL`), restricted variant: statement (definitions only, no proofs)

Source: `chapters/marl.tex:441–467` (theorem), context :425–440 (Q-FTRL described only informally,
"we omit full algorithmic details", :432), "uniformly over the entire accuracy range `ε ∈ (0,H]`"
:476, the commented-out sample-count remark "`KSHΣ_i A_i`" :480–481. Known rewards:
`chapters/generative_model_model_based.tex:31`. See `docs/SOURCE-ISSUES.md#C39`.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl77

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

end StatisticalRL.Ch7Rest.Marl77
