# Source issues and unresolved interpretation

This is a research ledger, not an author-approved errata list. The original
article remains the source of truth. A corrected result is separately identified
and must not be presented as a proof of an incorrect original statement.

## Candidate C1: singleton actions in Theorem 3.7(i)

**Source:** arXiv:2610.41903v1, printed pp. 47–48,
`chapters/generative_model_model_based.tex:1443–1464`, label `theorem:azar`.
The theorem itself quantifies over deterministic policy estimators with `SA ≥ 16` and
asserts a positive-probability event where the estimated policy's Q-value
differs from the optimal policy's Q-value by more than a positive ε. The printed
statement has no explicit exclusion for `A = 1`. The preceding policy-learning
section assumes `A ≥ 2` (`chapters/generative_model_model_based.tex:787`),
and whether that restriction carries into the next section is an unresolved
interpretation question. Under that standing assumption this singleton-action
case is outside the policy-learning domain.

Set `S = 16`, `A = 1`. Every deterministic policy is the same function, so
for every MDP and every data-dependent policy estimator, the error event is
empty. Choosing ε small enough also satisfies the sample-size upper bound for
any fixed positive constant and any chosen positive integer sample count. The
code in `Formalization/Obstructions/SingletonAction.lean` proves the relevant
policy-evaluation equality and zero event measure for arbitrary extensional
evaluation maps and confirms the cardinality inequality. It does not yet
formalize the full sample experiment or its quantifier structure.

**Status:** a contradiction under the standalone reading of the theorem was
reconstructed from raw TeX and visually checked in the PDF. The scope of the
preceding section's assumption, full formal encoding, and independent review remain
open. Treat `A ≥ 2` as an explicit interpretive choice rather than silently
introducing it or claiming an author-approved correction.

## Candidate C2: one state and known rewards in Theorem 3.7

Independent [source review](critic-one-state-review.md) finds that both parts
of the theorem are contradicted by `S = 1`, `A = 16` under the source's
known-reward convention. The only transition law returns to the sole state;
the single estimator `Q̂(a) = r(a) + γ max_b r(b)/(1−γ)` can use the known
reward and is exact for every admissible model and dataset. A fixed
tie-breaking reward-greedy policy is likewise optimal. The earlier `A ≥ 2`
policy-learning convention is satisfied by this example.

For every proposed constant `c_N > 0`, the reviewer chooses `γ = 2/3`, `N = 1`
and a sufficiently small positive ε satisfying the printed sample and accuracy
restrictions. This numerical feasibility is now proved for every positive
constant in [OneStateParameters.lean](../Formalization/Obstructions/OneStateParameters.lean)
and checked in an [independent review](critic-one-state-parameters.md). The construction used in the paper's proof also degenerates at
`S = 1`: it yields one hypothesis where the Fano step requires at least four.

`Formalization/Obstructions/OneState.lean` establishes the exact formula and
greedy policy for the Bellman fixed points; the trajectory and experiment
bridges below extend the evidence to actual infinite trajectories and a
one-sample generative experiment. An [independent Lean review](critic-one-state-lean-review.md)
checks the original Bellman-level claims. Exact equivalence between the encoded
negation and every source estimator and policy convention remains unresolved,
so this is not presented as a complete Lean refutation of the printed theorem.
`S ≥ 2` excludes this example but is not asserted sufficient for the original
result. No author-approved correction or ruling is assumed.

## Candidate repair of Theorem 3.7

A [proposed correction](critic-theorem37-correction.md) adds `S ≥ 2` and
`A ≥ 2` to the combined statement and supplies a conservative constant
`c_N = 1/8192`, with separate arguments for policy learning and Q estimation.
It also repairs an incorrect expression for the optimal Q-value after a
suboptimal first action, the source's hypothesis count in its Fano step, and
the policy decoder. A separate [mathematical check](critic-theorem37-correction-independent.md)
reproduces the probability bounds and constants; a further [independent audit](critic-theorem37-final-audit.md) checks the model and estimator quantifiers. This is a proposed replacement,
not an author-approved erratum or a completed Lean proof; the full statistical
experiment and its testing reductions still need formal verification. The
[one-state trajectory bridge](../Formalization/Obstructions/OneStateTrajectory.lean)
proves exactness of a fixed known-reward estimator and its zero error under
any data law ([review](critic-one-state-trajectory.md)). The
[one-state experiment](../Formalization/Obstructions/OneStateExperiment.lean)
constructs actual independent samples and packages the uniform estimator and
feasible parameters ([review](critic-one-state-experiment.md)); [Theorem37Negation.lean](../Formalization/Obstructions/Theorem37Negation.lean)
negates an encoded source-facing version; its estimator-interface and policy
interpretations are not certified as exactly equivalent to the source ([audit](critic-theorem37-negation.md)). The
[policy experiment](../Formalization/Obstructions/OneStatePolicyExperiment.lean)
likewise gives a measurable reward-greedy estimator with zero actual Q loss
([review](critic-one-state-policy-experiment.md)). The
correct two-state Bellman values and source-range policy loss are proved in
[HardMDP.lean](../Formalization/Obstructions/HardMDP.lean), with an
[independent review](critic-hard-mdp.md). The separate
[trajectory optimality result](../Formalization/MDP/OptimalTrajectoryValue.lean)
applies to the stationary policy class; the multi-model statistical reduction
remains to be formalized.

The initial review additionally records uncertainty over a confidence-radius
scaling in Section 7.4 and a reward-convention conflict in Section 7.2. Those
observations require further independent verification.

## Candidate C3: omitted sample-size case in policy evaluation proof

**Source:** `chapters/generative_model_model_based.tex:589–634`, especially
`eq:T2-bound` and `eqn:ice-cream`. The displayed intermediate bounds assume
`N ≥ 64β₁/(1−γ)`, but the final estimate is stated for
`N ≥ β₁/(1−γ)` without an explicit argument covering the intervening range.
This is a gap in the displayed derivation, not a counterexample to the final
claim. The source uses the same β₁ before and after this step.

**Proposed proof repair:** both the true and empirical policy values lie in
`[0, 1/(1−γ)]`, so their sup-norm difference is at most `1/(1−γ)`.
The printed final radius `3√(8β₁/((1−γ)³N))` is at least this bound when
`N ≤ 72β₁/(1−γ)`. A deterministic low-sample case thus covers the omitted
range, while retaining the original high-sample argument and final constants.
This repair does not by itself justify each intermediate bound under the weaker
threshold. The independent [mathematical review](critic-policy-evaluation-sample-constant.md)
checks the argument and the strict-probability issue; full formal integration
of the repair and the sharp statistical theorem remain separate obligations.
