# Builder notes: finite MDP foundations

Source: arXiv:2610.41903v1, `source/upstream/tex/chapters/prelim.tex`.
These notes describe builder evidence, not an independent source audit or a
claim of complete Chapter 2 coverage.

## Definitions and exact source correspondence

| Source range / label | Lean object | Scope |
|---|---|---|
| Lines 31–52: finite state/action sets, stochastic kernel, rewards in `[0,1]`, `0 ≤ γ < 1` | `StatisticalRL.DiscountedMDP` | Exact model data and bounds. Nonempty carrier fields exclude empty MDPs. Arbitrary finite types may be instantiated by the source's numbered state/action sets. |
| Lines 65–75, `eq:defn-P-s-pi-inf` | `StationaryPolicy`, `DiscountedMDP.policyTransition` | Randomized policies and their actual finite-mixture transition distribution; normalization is proved by `FiniteDistribution.bind`. |
| Lines 188–196, `eq:bellman_consistency_operator` | `DiscountedMDP.qBellman` | Actual nested finite probability expectations. |
| Lines 219–222, `eq:bellman_consistency-V-all` | `DiscountedMDP.valueBellman` | The state-value backup operator only. |
| Lines 235–239, `eq:bellman_optimality_operator` | `DiscountedMDP.qOptimality`, `actionMaximum` | A genuine maximum on the nonempty finite action set; no default action or fallback value. |
| Lines 253–283, `eq:gamma-contraction-preliminary-inf` and its proof | `DiscountedMDP.norm_qBellman_sub_le`, `norm_qOptimality_sub_le` | Both displayed supremum-norm contraction bounds are proved. Lean's finite Pi norm is the maximum absolute-entry norm. |
| Lines 209, 242–245: uniqueness assertions | `DiscountedMDP.qBellman_fixedpoint_unique`, `qOptimality_fixedpoint_unique` | At-most-one fixed point, derived from strict contraction. Existence and identification with trajectory returns remain open. |
| Lines 663–696: nonstationary finite-horizon model and policy | `StatisticalRL.DecisionStage` | Every actual stage stores its own kernel, reward and policy; reward bounds and nonempty carriers are explicit. |
| Lines 784–791, terminal-zero condition and `eq:Bellman-finite-pi` | `DecisionStage.qBackup`, `valueBackup`, `backwardValue` | A backward-evaluation algorithm on the actual list of remaining stages. Its empty suffix is the terminal stage. Identification with independently defined expected trajectory returns is not yet proved. |

`FiniteDistribution` is the finite real probability simplex: nonnegative
weights summing to one. Its `expectation` is the actual weighted sum.
Linearity, monotonicity, bounded-expectation inequalities, mixture normalization,
and the iterated-expectation identity `expectation_bind` are proved directly.
No probability or Bellman law is assumed as an extra hypothesis.

`backwardValue_nonneg` and `backwardValue_le_length` establish that the
backward evaluator lies in `[0, number of remaining stages]`.
These bounds do not on their own prove the paper's trajectory-value claims.

## Singleton-policy challenge

`deterministic_policy_eq_of_subsingleton` proves that every two deterministic
policies on a singleton action carrier are equal. It is a general fact about
the actual function space, independent of model details. The companion
`FiniteDistribution.prob_eq_one_of_subsingleton` proves that the only action
has probability one under every finite randomized policy. These are available
for independently checking the critic's singleton-action lower-bound challenge.

## Validation

Both files compiled successfully, sequentially, with:

```sh
bash scripts/lean-local.sh -o .lake/build/lib/lean/Formalization/MDP/Basic.olean Formalization/MDP/Basic.lean
bash scripts/lean-local.sh -o .lake/build/lib/lean/Formalization/MDP/FiniteHorizon.olean Formalization/MDP/FiniteHorizon.lean
```

This uses the pinned Lean `v4.27.0-rc1` compiler and read-only cached packages.
No dependency rebuild, toolchain change, custom axiom, `sorry`, or `admit` was used.
An ephemeral `#print axioms` probe imported `Formalization.MDP.FiniteHorizon`
and checked the mixture theorem, both singleton lemmas, maximum perturbation,
all three norm contraction bounds, both fixed-point uniqueness results,
finite-stage nonexpansiveness and both backward-value bounds. The probe exited
successfully; every reported closure was a subset of `propext`,
`Classical.choice`, and `Quot.sound`. The probe was removed afterwards.
The parent integration check and independent critic review remain necessary.

## Open obligations

- Define actual infinite trajectory laws and expected discounted returns, prove
  summability, and identify them with Bellman fixed points.
- Prove fixed-point existence, deterministic optimal-policy existence, occupancy
  laws, matrix/resolvent formulations, dynamic-programming convergence, and the
  remainder of Chapter 2.
- Connect finite backward evaluation with a separately constructed trajectory
  expectation and the source's exact indexed value/Q-value definitions.
- Formalize all later sample-complexity, regret, lower-bound, extension and
  appendix results; this foundation does not establish those results.
