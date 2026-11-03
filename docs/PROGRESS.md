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
- `Formalization/Obstructions/SingletonAction.lean` proves a singleton-action
  policy-loss obstruction; [SOURCE-ISSUES.md](SOURCE-ISSUES.md) records the
  unresolved question of whether Section 3.3's `A ≥ 2` assumption carries
  forward to the lower-bound theorem in Section 3.4.
- The pinned Lean toolchain compiled the eight current project modules; the
  transitive axiom audit checked 199 project declarations, allowing only
  `propext`, `Classical.choice`, and `Quot.sound`. These checks do not replace
  source review. Current builder work and independent critic findings are
  recorded separately in `builder-*.md` and `critic-*.md`.

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
