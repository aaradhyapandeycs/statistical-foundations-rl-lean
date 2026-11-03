# Whole-monograph progress

Status: **active; incomplete**. Source: arXiv:2610.41903v1, 326 PDF pages.

No whole-paper or chapter completion is certified. Source-level claims need
an exact Lean statement, all mathematical prerequisites, compilation, an axiom
audit, and independent correspondence review before promotion.

## Current checked infrastructure

- A reproducible lexical inventory covers the active source include tree. It
  identifies 90 named theorem/lemma/claim environments, 17 algorithms, 1,381
  display environments, and numerous further candidate obligations. These are
  scanner counts, not a proof-coverage percentage or a semantic completeness
  claim. All inventory items remain unformalized/unreviewed pending review.
- `Formalization/MDP/Basic.lean` defines finite stochastic kernels, policies,
  and Bellman maps; it proves both policy and optimality contraction bounds.
- `Formalization/MDP/FixedPoint.lean` proves Bellman fixed-point existence,
  uniqueness, geometric iteration bounds, and interval bounds. Identification
  with infinite-trajectory Q-values and optimal-policy existence remain open.
- `Formalization/MDP/FiniteHorizon.lean` and `FiniteTrajectory.lean` construct
  nonstationary finite trajectories and prove that their expected cumulative
  reward equals backward evaluation. Finite-horizon optimality remains open.
- `Formalization/MDP/FiniteQTrajectory.lean` additionally constructs the
  action-conditioned trajectory law, proves both indexed finite-horizon policy
  Bellman equations, and supplies zero terminal values.
- `Formalization/MDP/FiniteOptimal.lean` constructs a greedy deterministic
  stage sequence in one common, time-varying environment, proves it dominates
  randomized Markov policies, and derives the finite optimal Bellman equations.
  The [independent review](critic-finite-optimal.md) identifies the finite
  policy representation and zero-horizon boundaries that remain to address.
- `Formalization/MDP/FiniteOccupancy.lean` constructs finite state and
  state-action occupancy laws and proves their factorization and initial-state
  identity. The [independent review](critic-finite-occupancy.md) identifies
  the still-missing full-episode event bridge and optimal-policy specialization.
- `Formalization/MDP/DiscountedFiniteTrajectory.lean` defines discounted
  rewards on actual finite trajectory laws, proves their Bellman recursion,
  and proves that finite expectations converge to the unique state Bellman
  fixed point. Its [independent review](critic-discounted-finite.md) checks
  the finite-law semantics and discount exponents. The infinite-path expectation
  and its interchange with the limit have not yet been constructed.
- `Formalization/Probability/Variance.lean` proves the source's exact finite
  transition-variance perturbation bound, Lemma 2.2. See its independent
  [scoped review](critic-variance-review.md).
- `Formalization/Obstructions/SingletonAction.lean` proves a singleton-action
  policy-loss obstruction. `Obstructions/OneState.lean` proves a one-state
  Bellman fixed-point formula and optimal greedy policy. See
  [SOURCE-ISSUES.md](SOURCE-ISSUES.md) for the source review, including a
  one-state counterexample under the known-reward convention and the pending
  Lean bridge to the full statistical theorem.
- The current pinned Lean integration compiled fourteen project modules; its
  transitive axiom audit checked 364 project declarations, allowing only
  `propext`, `Classical.choice`, and `Quot.sound`. These checks do not replace
  source review. Current builder work and independent critic findings are
  recorded separately in `builder-*.md` and `critic-*.md`.
- The [trajectory critic review](critic-trajectory-review.md) checked path
  weights, reward order, terminal marginalization, and two concrete Lean
  examples. Its reviewer authored the imported basic MDP dependencies, whose
  separate review remains necessary. The review also confirms that the
  singleton-action obstruction depends on the source interpretation.
- A separate [fixed-point critic review](critic-fixedpoint-review.md) checked
  the source-facing model fields, finite supremum norms, Bellman contractions,
  fixed-point selection, and the γ = 0 boundary. It passes those scoped
  infrastructure claims while leaving source trajectory semantics and policy
  iteration open.
- The [finite-Q critic review](critic-finite-q-review.md) checks the indexed
  policy Bellman equations against the actual action-conditioned trajectory law.
  Whole-chapter and infinite-horizon completion remain open.

## Teams and ownership

| Role | Owned work | Current objective |
|---|---|---|
| Lead builder/integrator | project configuration, checking, analysis infrastructure | reproducible proof environment and integration |
| Source builder | `scripts/inventory.py`, `docs/source-inventory.*` | complete source traversal and explicit coverage checklist |
| MDP builder | `Formalization/MDP/Basic.lean`, `FiniteHorizon.lean` | faithful finite tabular model and Bellman foundations |
| Independent critic | `docs/critic-initial-review.md` | reconstruct claims from source and challenge semantics and coverage |

## Required coverage

1. Introduction: mathematical conventions and substantive claims.
2. Preliminaries: MDP semantics, policies, value/Q functions, occupancy,
   Bellman and planning theory, concentration and testing inequalities.
3. Generative-model model-based algorithms, upper and lower bounds, and appendices.
4. Generative-model model-free algorithms, TD, Q-learning, and appendices.
5. Online RL, bandits, UCB-VI, MVP, model-free methods, lower bounds, and appendices.
6. Offline RL, pessimism, model-based/model-free methods, lower bounds, and appendices.
7. Robust, competitive multi-agent, federated, inference, and human-feedback extensions.
8. Concluding mathematical claims and all externally cited substantive inputs.

Every chapter remains open. Algorithm and trajectory semantics must be
connected to probabilistic guarantees; abstract helper bounds alone do not
certify an RL theorem. Externally cited mathematics is an obligation to prove
or instantiate from an audited dependency, not a new project axiom.
