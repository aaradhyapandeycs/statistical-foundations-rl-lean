# Independent review: trajectories, contractions, and singleton-policy challenge

Date: 2026-11-02. Source: unmodified arXiv:2610.41903v1 TeX under
`source/upstream/tex/chapters/`.

The reviewer did not author the three modules reviewed here. The reviewer did
author the imported `MDP/Basic.lean` and `MDP/FiniteHorizon.lean`; this review
therefore does not independently certify those dependencies. Their separate
source audit and the lead's complete integration check remain necessary.

## Verdicts

| Target | Verdict | Scope |
|---|---|---|
| `Formalization/MDP/FiniteTrajectory.lean` | **PASS: component semantics** | Genuine finite path law, expected cumulative reward, and its equality with backward evaluation for arbitrary stage-dependent randomized policies. |
| `Formalization/Analysis/Contraction.lean` | **PASS: generic infrastructure** | Correct iteration bound and contraction fixed-point existence/uniqueness with the necessary completeness and nonempty-space hypotheses. |
| `Formalization/Obstructions/SingletonAction.lean` | **PASS: mathematical obstruction lemmas** | Singleton policies have identical extensional evaluations, so the positive-loss event is empty and has measure zero under every measure. |
| Unqualified claim that these lemmas certify a defect in the entire source theorem | **FAIL without a source-scope qualification** | The source previously introduces policy learning with `A ≥ 2`; whether that convention carries into the later lower-bound theorem must be resolved explicitly. The standalone theorem text omits this restriction. |

These passes do not seal a whole source theorem or Chapter 2.

## Finite trajectory reconstruction

The source gives nonstationary kernels/rewards at each time
(`prelim.tex:663–687`), randomized policies `π_h(·|s)` (`695–696`), and
expected cumulative reward from the supplied initial state (`707–716`). Its
finite Bellman recursions use terminal value zero (`784–791`).

The implementation preserves these semantics:

- `FinitePath n` stores exactly `n` action/next-state pairs; the current state
  is supplied separately. The empty path is the terminal suffix, not an
  invented zero-valued branch outside an unfinished construction.
- `pathWeight` (`FiniteTrajectory.lean:71–76`) multiplies the current-state
  policy probability, the actual transition probability for the selected
  action, and the tail probability evaluated at the **sampled next state**.
  It does not incorrectly reuse the initial state or first-stage policy.
- `pathReward` (`79–83`) adds the current state/action reward before passing
  the sampled next state to the next, potentially different stage.
- `sum_pathWeight` (`96–106`) proves full normalization. The path stores a
  final transition after the last rewarded action; this extra terminal state
  is harmless because its conditional probabilities sum to one and the
  terminal reward is zero. No final reward is omitted or counted twice.
- `trajectoryLaw` and `trajectoryValue` (`109–117`) are an actual normalized
  finite probability vector and its weighted expectation. Their definitions
  precede and do not assume the Bellman identity.
- `trajectoryExpectation_cons` (`121–132`) proves first-step conditioning for
  every whole-path payoff by finite-sum rearrangement. The reward-specific
  decomposition (`141–151`) and equality with backward evaluation (`155–161`)
  then follow from normalization and induction. No extra theorem-shaped
  hypothesis or assumed return identity is hidden in the signatures.

Two independent temporary Lean probes expanded the raw weighted sums directly,
without using `trajectoryValue_eq_backwardValue` or the Bellman decomposition:

1. One state-conditioned stage with two equiprobable actions, rewards `0`
   and `1`, and a normalized final transition has expected return `1/2`.
2. A two-stage Boolean-state model starts at `false`, transitions to `true`
   after a zero reward, and then uses a state-dependent policy selecting the
   action equal to its current state, with action-`true` reward `1`. Expected
   return is `1`. Reusing the initial state for the tail policy would give `0`.

Both probes compiled successfully. A further probe transported the existing
backward bounds to obtain `0 ≤ trajectoryValue ≤ number of remaining stages`.
This is meaningful evidence for randomized-policy averaging, next-state
dependence, terminal marginalization and reward indexing; it is not exhaustive
coverage of all source claims.

## Singleton-action event and source qualification

The obstruction has no mathematical gap: on a singleton action carrier every
function `State → Action` is equal. Consequently any extensional evaluation
map gives zero norm loss for every observation and every estimator. For
positive `ε`, the failure event is literally empty. Its measure is zero
without needing an estimator-measurability assumption. Choosing
`State = Fin 16`, `Action = Fin 1` satisfies the standalone cardinal product
restriction `SA ≥ 16`.

The source-interpretation caveat is material:

- `generative_model_model_based.tex:787` explicitly starts policy learning
  with `A ≥ 2`.
- The later theorem `theorem:azar` (`1443–1464`), in a new section beginning
  at `1438`, repeats `SA ≥ 16` but does not repeat `A ≥ 2`. Its part (i) has
  precisely the deterministic-policy loss challenged by the Lean lemma.
- Immediately afterwards, line `1472` also discusses `A = 1` for **policy
  evaluation**, a distinct task. This does not settle whether the part-(i)
  policy-learning statement inherits the earlier restriction.

Therefore the Lean result establishes a decisive challenge to a standalone
transcription admitting `A = 1`. It does not establish that the paper's
authors intended that domain, nor certify an erratum after all standing
conventions. Use wording such as “singleton-action obstruction if the theorem
is read with only its displayed size restriction,” retain the source context,
and obtain an explicit interpretation before changing a source-facing type.

A complete formal refutation of a fully specified minimax theorem would also
instantiate the actual statistical experiment and sample-count/parameter
quantifiers. Those objects are not asserted by this elementary obstruction
module.

## Contraction review

`iterate_dist_le` correctly iterates a Lipschitz bound against a separately
supplied fixed point. It is valid for any nonnegative Lipschitz constant and
does not silently assume that the target is the source's optimal return.
`contraction_fixed_unique` uses strict contraction. Existence is proved only
with `Nonempty X` and `CompleteSpace X`, and is obtained from Mathlib's
fixed-point theorem, not a field assuming the desired source conclusion.
The module correctly disclaims policy iteration and trajectory identification.

## Remaining source obligations

- Give the exact original `h ∈ [H]` interface, mapping a full nonstationary
  model/policy to its suffix of stages, and preserve all state/time quantifiers.
- Construct action-conditioned finite Q-return semantics and prove both
  equations in `eq:Bellman-finite-pi`; the reviewed file establishes the
  state-return decomposition, not this full paired claim.
- Supply the initial-distribution form `eq:defn-V-rho-finite`, finite optimal
  deterministic policy and occupancy laws, and associated source interfaces.
- Construct the infinite discounted trajectory law/return, summability and
  its equality to the Bellman solutions. Generic contraction and finite
  trajectories do not establish that infinite-horizon bridge.
- Preserve a single environment when comparing policies. A `DecisionStage`
  list packages the policy with the kernel/reward, so future optimality
  comparisons need explicit common-environment data rather than arbitrary
  comparisons between unrelated stage lists.

## Verification evidence

The temporary probe was checked using `bash scripts/lean-local.sh` with the
pinned compiler and current compiled imports. It exited successfully.
`#print axioms` checks of `trajectoryValue_eq_backwardValue`,
`singleton_action_failure_measure_eq_zero`, and `contraction_exists_unique`
reported only `propext`, `Classical.choice`, and `Quot.sound`. The probe was
removed. This review did not rerun the complete repository build; the lead
must perform that integration check on the exact released source tree.
