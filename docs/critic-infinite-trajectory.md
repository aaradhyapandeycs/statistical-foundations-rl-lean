# Independent source review: infinite trajectory law

## Source-first reconstruction

`prelim.tex` lines 31–52 gives finite state/action carriers, a normalized
transition distribution `P(·|s,a)`, a deterministic reward in `[0,1]`, and
`γ ∈ [0,1)` for the stationary discounted MDP. Lines 66–73 define a
state-dependent randomized stationary policy `π(·|s)`. Lines 89–102 specify
the trajectory: start from an initial state (or a given distribution over
states, lines 107–110), draw `a_t` from `π(·|s_t)` and then `s_{t+1}` from
`P(·|s_t,a_t)` at every `t ≥ 0`. To represent this as a probability law on
`ℕ → State × Action`, the initial pair law must assign `ρ(s)π(a|s)` and the
transition from `(s,a)` to `(s',a')` must assign
`P(s'|s,a)π(a'|s')`; every such distribution must be nonnegative and normalized.
A point initial state and a probability initial distribution are both source
interfaces. Every finite-dimensional prefix law must preserve the initial
state/action order and agree with these kernels; the empty-prefix probability is
one. Conditioned on a positive-probability history, the next-pair distribution
must be the transition kernel above. Separate forced-first-action continuation
is required to interpret Q for actions even when their policy probability is
zero (lines 114–123); it cannot be justified by division by zero.

The source's value and Q are expectations of an infinite discounted sum (lines
93–102 and 114–123), not merely the existence of a path law or finite prefix
agreement. Those semantic results require separate convergence, measurability,
integrability, and conditioning arguments unless the checked implementation
actually provides them. The law alone also does not establish an optimality
claim or a generative-model statistical experiment.

Source SHA-256: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.

## Findings

**Verdict: PASS for the explicitly scoped fixed-initial-state infinite path
measure, first-step marginal, general Mathlib-kernel prefix identity, and
history/next-step joint identity.** The stronger bridges below remain open;
this is an independent semantic review, not a frozen-statement audit.

1. `DecisionStage.stepDistribution` (InfiniteTrajectory.lean lines 22–30)
   gives probability `π(a|s)P(s'|s,a)` to `(a,s')` and proves both
   nonnegativity and total mass one. `FiniteDistribution.toPMF` (32–42)
   converts the real masses via `ENNReal.ofReal`; nonnegativity and the sum
   proof ensure the conversion neither truncates a negative mass nor changes
   normalization. The fixed model's `stationaryStage` copies the original
   transition and policy, so the one-step law is the intended model, not an
   arbitrary replacement.
2. The measurable spaces on the two finite carriers are locally discrete
   (`⊤`, lines 46–47). `stepMeasure` (49–57) is a probability measure.
   `historyKernel` (59–72) is a Markov kernel on every finite history and uses
   the previous pair's second component as the state for the next action. No
   per-state positivity, irreducibility, or extra sampling assumption appears.
   The model structure supplies nonempty state and action carriers and actual
   normalized finite probability vectors.
3. `infiniteTrajectoryLaw` (74–84) genuinely invokes Mathlib's Ionescu–Tulcea
   `Kernel.trajMeasure`, with the initial step `π(a₀|s₀)P(s₁|s₀,a₀)` and the
   history kernels. The instance proves it is a probability measure. The
   coordinate convention is `(a₀,s₁),(a₁,s₂),…` with the initial state `s₀`
   retained as an external parameter. This is equivalent in content to the
   source's `(s_t,a_t)` convention once indexed appropriately; the source's
   state `s_t` at positive times is the preceding coordinate's second component.
   `stepMeasure_singleton` (86–93) checks the actual first-step mass.
4. `infiniteTrajectoryLaw_prefix` (95–104) identifies the inclusive prefix
   `0,…,n` with Mathlib's `partialTraj` started at the initial step. This is
   a genuine *all n* theorem about the iterated Mathlib history-kernel law; it
   is not an all-length theorem equating that law with the project's separate
   recursive `DecisionStage.trajectoryLaw`. Such an equality is exported only
   at one stage in `infiniteTrajectoryLaw_one_prefix` (121–146). In
   particular the all-length bridge needed to transport arbitrary finite-path
   expectations is not yet a Lean theorem. The case `n=0` is one sampled pair,
   not an empty prefix; total probability one follows separately from the
   probability-measure instance.
5. `infiniteTrajectoryLaw_history_step` (155–161) identifies the joint
   history/next-coordinate law with its composition product using the stated
   kernel. This does not assert a numerical conditional probability at
   zero-probability histories. A separate temporary compiled probe instantiated
   Mathlib `Kernel.condDistrib_trajMeasure`: the regular conditional
   distribution of the next pair given the observed prefix agrees almost
   everywhere with `historyKernel`. The finite history carrier then makes the
   usual formula available at positive-mass histories. The almost-everywhere
   qualification matters; no assertion about a uniquely determined
   conditional at a zero-mass history follows.
6. The exported infinite law starts from a supplied point state, matching the
   source's state-conditioned V definition. It does **not** construct an
   arbitrary initial-distribution mixture as a named law; such a mixture is a
   separate representational/connection task. Nor does it provide a
   forced-first-action infinite law for every `(s,a)`, which is needed to give Q
   trajectory semantics even when `π(a|s)=0`. These absences do not invalidate
   the fixed-state path law.
7. No infinite discounted reward random variable, its measurability or
   integrability, expected infinite return, limit/prefix-expectation theorem,
   or identity with Bellman fixed points is defined or proved in this module.
   Thus neither source V/Q trajectory semantics nor the statistical minimax
   counterexample can be reported as completed based on this law alone.

The source-facing inputs are finite carriers and Fintype instances, a
`DiscountedMDP` whose fields enforce nonempty carriers, valid finite transition
probabilities, bounded reward and `0 ≤ γ < 1`, an arbitrary normalized
stationary policy, an initial state, and the natural prefix index. The law's
kernel itself does not use reward or discount, but those are source model fields
rather than extra analytic premises. There are no assumed trajectory or
conditional-distribution identities.

## Validation and identity

A copy of the exact reviewed source bytes with appended probes was compiled via
`bash scripts/lean-local.sh <temporary-probe>`. It
checked the almost-everywhere conditional-distribution consequence described
above. The eight `#print axioms` checks on `stepDistribution`, `toPMF`,
`infiniteTrajectoryLaw`, `stepMeasure_singleton`, `infiniteTrajectoryLaw_prefix`,
`infiniteTrajectoryLaw_first`, `infiniteTrajectoryLaw_one_prefix`, and
`infiniteTrajectoryLaw_history_step` used only `propext`, `Classical.choice`,
and `Quot.sound`. The temporary file was removed. This checks an exact source
copy with imports, not a separate facade or integration build.

SHA-256:

- `Formalization/MDP/InfiniteTrajectory.lean`: `60c4f2c0279014ba54f6d0165e01d86ba407f2f72f93f4e9c493a6b8b86e33e9`
- `Formalization/MDP/DiscountedFiniteTrajectory.lean`: `c6b25ae5dfc3dc38f1d4ae654524764e10474ba04d94a0925242de5d88ccbdd6`
- `Formalization/MDP/FiniteTrajectory.lean`: `5b6f53bc1822729beb715ad385b74951dedf7c0596ca654cf246945593ca3130`
- `Formalization/MDP/Basic.lean`: `ecf28ee04a78405be352f5453d957f34a7883d33304b21255a9f7f444e0bc088`
