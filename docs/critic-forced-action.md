# Independent review: forced-first-action infinite trajectory

**Verdict: PASS for the stated forced-first-action probability law and its initial/joint-history identities.** The source's infinite-Q reward expectation and its Bellman identification have **not** been proved by this module. This is a scoped independent review of the staged file, not an author-approved frozen-statement audit or whole-paper certification. The reviewer did not author the staged file.

## Source-first reconstruction and interpretation

`source/upstream/tex/chapters/prelim.tex:31–52` gives finite, nonempty state/action spaces, normalized stochastic transitions, deterministic stationary rewards in `[0,1]`, and `0 ≤ γ < 1`. A stationary randomized policy supplies a normalized action distribution at each state (lines 63–74). The source defines `Q^π(s,a)` by the expected infinite discounted return given first state s and action a (114–120), and explicitly explains that action a is taken first and subsequent actions are drawn from π (line 123). The initial transition must therefore use `P(·|s,a)`, and for `t ≥ 1` the policy must use the state actually reached before its action.

For an action with `π(a|s)=0`, the source's displayed conditional-expectation notation is not by itself a uniquely defined ordinary conditional probability on that zero-probability event. Its prose supports the forced-first-action/intervention construction for all actions. This module constructs that law directly, without division by `π(a|s)` or a positive-support hypothesis. It does not prove an equality with an arbitrary version of conditioning on a null event; no such equality is claimed by this review.

## Expanded definitions and findings

- The existing `DecisionStage.stepDistribution` in `Formalization/MDP/InfiniteTrajectory.lean:22–30` gives `(a,t)` mass `(π s).prob a * (M.transition s a).prob t`, proves nonnegativity and normalization, and `stepMeasure` converts that real finite distribution to a PMF-backed probability measure. `stepMeasure_singleton` (88–93) proves that exact singleton mass. `EnvironmentStage.pointMass a` (`FiniteOptimal.lean:86–94`) is a real finite distribution concentrated on a, not a hypothetical action supplied by a premise.
- `forcedActionTrajectoryLaw` (staged lines 16–21) applies `Kernel.trajMeasure` to the initial `stepMeasure` using the constant point-mass policy `fun _ ↦ pointMass a`, **then** uses the original `M.historyKernel π`. The first-state input is s and the forced point mass applies only to the initial step. Its probability-measure instance (23–27) uses the actual normalized initial distribution and Markov history kernels.
- In `InfiniteTrajectory.lean:59–72,148–153`, `historyKernel π n` applies the **original** π at the next stage using the state component of history's last recorded `(action,next-state)` pair. The stationary model's original transition kernel is used for the selected later action. Thus there is no accidental reuse of the initial state, forced action, or a new policy at later times. The law's index 0 stores `(a₀,s₁)`; its index `n+1` is sampled after history through n, so the first policy-controlled action occurs at index 1.
- `forcedActionTrajectoryLaw_first` (30–43) derives that the first-pair marginal is the forced step law. `forcedActionTrajectoryLaw_first_pair` (45–53) derives, for every b and t, mass `if b=a then ofReal(P(t|s,a)) else 0`. This explicitly covers actions of zero probability under π and zero-probability successor states. Normalization of `P(·|s,a)` implies the first action is forced with total probability one; the latter summation is a mathematical consequence of the first-marginal result, not a separate exported theorem here.
- `forcedActionTrajectoryLaw_history_step` (55–62) gives equality of measures between the composition-product of the whole prefix law with `M.historyKernel π n` and the joint law of that prefix and the next pair. It uses Mathlib's Ionescu–Tulcea trajectory-law theorem, rather than assuming a conditional independence hypothesis. It is an unconditional joint-measure identity; it does not divide by the probability of a history, so zero-mass histories cause no issue.

The quantified `State`, `Action`, and finite instances are source carrier data; `M` expands to source transition/reward/discount fields and nonemptiness; `π` expands to genuine per-state finite probability vectors; `s`, `a`, `b`, `t`, and `n` are arbitrary source variables and indices. No support condition, new policy premise, independently assumed product law, fixed-point equality, or claimed infinite-return equality is hidden in a binder.

## Independent check and exact identity

A temporary copy of the **exact staged source** `Formalization/MDP/ForcedActionTrajectory.lean` was compiled with `bash scripts/lean-local.sh <temporary-file>`, with the following appended test: choose distinct actions `a ≠ b`, let π be the point-mass policy at b, and establish simultaneously that `(π s).prob a = 0` and that the forced law's first-pair singleton `(a,t)` has mass `ofReal(P(t|s,a))`. The source and test compiled without diagnostics. The same probe ran `#print axioms` for `forcedActionTrajectoryLaw_isProbabilityMeasure`, `forcedActionTrajectoryLaw_first`, `forcedActionTrajectoryLaw_first_pair`, and `forcedActionTrajectoryLaw_history_step`; all four use only `propext`, `Classical.choice`, and `Quot.sound`. The temporary probe was removed. This recompiles the exact staged declarations and checks their axioms; it is not a separate import of a built module or an integration build.

Reviewed SHA-256 values:

| File | SHA-256 |
| --- | --- |
| `Formalization/MDP/ForcedActionTrajectory.lean` | `0844d90fa0f42b2eb739c82a0faf7bd8e8e26b31c2ae4399ad4261cafa239c90` |
| `Formalization/MDP/InfiniteTrajectory.lean` | `60c4f2c0279014ba54f6d0165e01d86ba407f2f72f93f4e9c493a6b8b86e33e9` |
| `Formalization/MDP/FiniteOptimal.lean` | `abd23ed8206032df152160f50d838d91bf99a169a09bbf2612bc5e9608494e85` |
| `Formalization/MDP/Basic.lean` | `ecf28ee04a78405be352f5453d957f34a7883d33304b21255a9f7f444e0bc088` |
| `Formalization/MDP/DiscountedFiniteTrajectory.lean` | `c6b25ae5dfc3dc38f1d4ae654524764e10474ba04d94a0925242de5d88ccbdd6` |
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` |

## Remaining semantic boundary

This module constructs and characterizes a probability law only. It does not define or prove measurability/summability of the infinite discounted reward along this forced law, take its expectation to define the source `Q^π`, or identify that expectation with `policyFixedPoint` or the source's Bellman equation. Nor does it prove an exact whole-prefix bridge to the separately constructed finite trajectory law. Those are separate integration obligations; the result here is not a proof of the source's full Q-value definition or of the V–Q expectation identity.

## Post-integration identity check

The integrated `Formalization/MDP/ForcedActionTrajectory.lean` has SHA-256 `77fe3fbe10217a1e8a6476a3ed1ea978c698c1972dec82b769f427491a9d9346`. A fresh complete textual diff against the reviewed staged file (SHA-256 `0844d90fa0f42b2eb739c82a0faf7bd8e8e26b31c2ae4399ad4261cafa239c90`) shows exactly three changes: explicit local names were added to the two `MeasurableSpace` instances and the `DecidableEq Action` instance. Their types, bodies, locality, and noncomputability are unchanged; no other source bytes differ. The preceding source-semantic review therefore applies to this integrated source, subject to the lead's integration compilation and axiom checks. The earlier compiled probe was performed on the staged source, not this renamed copy.
