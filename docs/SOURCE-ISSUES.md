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
greedy policy for the Bellman fixed points. Identification with the source's
infinite-trajectory optimal Q and formalization of the statistical experiment
remain open. An [independent Lean review](critic-one-state-lean-review.md)
checks the exact Bellman-level claims. The source
argument above is an independent mathematical review, not a complete Lean
refutation. `S ≥ 2` excludes this example but is not asserted to be sufficient
for the original result. No corrected theorem or author ruling is assumed.

## Candidate repair of Theorem 3.7

A [proposed correction](critic-theorem37-correction.md) adds `S ≥ 2` and
`A ≥ 2` to the combined statement and supplies a conservative constant
`c_N = 1/8192`, with separate arguments for policy learning and Q estimation.
It also repairs an incorrect expression for the optimal Q-value after a
suboptimal first action, the source's hypothesis count in its Fano step, and
the policy decoder. A separate [mathematical check](critic-theorem37-correction-independent.md)
reproduces the probability bounds and constants. This is a proposed replacement,
not an author-approved erratum or a completed Lean proof; the full statistical
experiment and its testing reductions still need formal verification. The
correct two-state Bellman values and source-range policy loss are proved in
[HardMDP.lean](../Formalization/Obstructions/HardMDP.lean), with an
[independent review](critic-hard-mdp.md). The separate
[trajectory optimality result](../Formalization/MDP/OptimalTrajectoryValue.lean)
applies to the stationary policy class; the multi-model statistical reduction
remains to be formalized.

The initial review additionally records uncertainty over a confidence-radius
scaling in Section 7.4 and a reward-convention conflict in Section 7.2. Those
observations require further independent verification.
