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

The source review also identifies a potential `S = 1` obstruction to Q-value
estimation in Theorem 3.7(ii), uncertainty over a confidence-radius scaling in
Section 7.4, and a reward-convention conflict in Section 7.2. See
`critic-initial-review.md` for scope and evidence. Those observations require
further independent verification.
