# Independent source review: forced-action infinite return

**Verdict: PASS for the intervention-based infinite trajectory Q expectation,
its integrability, geometric bounds and convergence of expected partial sums.**
Equality to a Bellman Q fixed point and the policy-average V–Q relation remain
separate obligations.

## Source-first reconstruction

`prelim.tex` lines 31–45 specifies finite state/action sets, stochastic
transition rows, rewards in `[0,1]`, and `0 ≤ γ < 1`. Lines 114–123 define
`Q^π(s,a)` through the discounted infinite trajectory return and specify that
action `a` is taken at `s` first, followed by policy `π` at later states. The
claim must quantify over *every* action, including actions having zero
probability under π. An intervention law supplies an unambiguous interpretation
on such zero-probability events; ordinary conditional probability is not
uniquely determined there. The law must use `P(·|s,a)` for the first
transition and the original policy thereafter. Its reward at `t=0` is
`r(s,a)`. The convergent sum is bounded between zero and `1/(1−γ)`; at `γ=0`
it reduces to `r(s,a)`.

## Findings

1. The imported `forcedActionTrajectoryLaw` in
   `Formalization/MDP/ForcedActionTrajectory.lean` uses the actual Ionescu–Tulcea
   measure, with a point mass at action `a` for the first action and the model
   transition for its next state. Its history kernel subsequently uses the
   original policy `π` and model transition at every reached state. Its
   probability-measure instance is specifically for this forced law. The
   `first_pair` identity gives zero mass for `(b,t)` when `b ≠ a` and mass
   `P(t|s,a)` when `b=a`, independently of `π(a|s)`; the separate review
   `docs/critic-forced-action.md` includes an explicit zero-policy-mass probe.
2. The imported path return from `InfiniteReturn.lean` uses the supplied
   initial state `s` at time zero and the preceding pair's next state at later
   times, paired with each current action. It proves every path's sum is
   summable, measurable, nonnegative and at most `1/(1−γ)`. Because this is a
   pointwise bound, `Formalization/MDP/ForcedActionReturn.lean` lines 23–31 correctly
   establishes integrability under the *forced* probability measure rather
   than transferring integrability from an unrelated policy measure.
3. `trajectoryExpectedQ` (33–37) is the actual integral of that return under
   the intervened law, for arbitrary `M`, `π`, `s`, and `a`. Its type contains
   no support premise, so it covers `π(a|s)=0`. This matches the source's
   all-action operational interpretation; it does not assert that an arbitrary
   version of a conditional expectation on a null event equals this value.
4. Lines 39–53 use dominated convergence on that same forced probability
   measure: measurable finite partial returns converge pathwise to the
   summable infinite return, and the common constant `1/(1−γ)` is integrable.
   The conclusion is convergence of their actual integrals. Lines 55–67 prove
   the exact nonnegative geometric bound using the forced law's probability
   normalization. There are no new probability, positivity, fixed-point,
   summability, or concentration assumptions.
5. An independent compiled probe verifies that for `γ=0` and any path whose
   first action is the forced `a`, the path return is exactly `r(s,a)`. The
   reviewed initial law makes that condition hold with probability one by
   finite normalization; no standalone γ=0 expectation theorem is exported
   by this staged file. There is no off-by-one loss of the first reward.
6. This module does not prove the Q Bellman equation or identify its integral
   with `policyFixedPoint`. It also does not prove `V^π(s) = E_{a∼π(s)}Q^π(s,a)`
   or provide the general finite-prefix bridge to the project's separate finite
   trajectory law. Those conclusions remain open, rather than being consequences
   of a definition alone.

The binders are the source finite carriers and model, an arbitrary normalized
randomized stationary policy and arbitrary state/action. The model's reward and
discount bounds support the convergence and integrability proofs. The forced
law introduces no artificial positivity condition.

## Checks and identity

A temporary copy of the exact staged source with a γ=0 pathwise consequence
and seven `#print axioms` checks compiled using
`bash scripts/lean-local.sh <temporary-probe>`. The checks
covered the forced-law probability instance, first-pair and history-step
identities, forced-return integrability, `trajectoryExpectedQ`, dominated
convergence and its geometric bound; each used only `propext`,
`Classical.choice`, and `Quot.sound`. The temporary file was removed. The
check recompiles a staged source copy with imported project artifacts; it is
not an integrated-export/facade build.

SHA-256:

- `Formalization/MDP/ForcedActionReturn.lean`: `87f447460f55da6d49a7311a73d69537f934395d3fbadf9c7a88b0c0c4bca0c2`
- `Formalization/MDP/ForcedActionTrajectory.lean`: `77fe3fbe10217a1e8a6476a3ed1ea978c698c1972dec82b769f427491a9d9346`
- `Formalization/MDP/InfiniteReturn.lean`: `0892b7c828e27835d4ee0f0ba48a5876bc26f05a92790da51f47df09e0730c8c`
- `source/upstream/tex/chapters/prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`
