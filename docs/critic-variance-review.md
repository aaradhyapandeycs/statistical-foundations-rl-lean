# Independent review: variance perturbation

The lead reviewed this module after a separate builder implemented it. This is
an infrastructure and statement review, not a frozen-anchor audit or a claim
that the rest of Chapter 2 is complete.

## Source reconstruction

`chapters/prelim.tex:427–445` defines each transition-row variance as the
second moment minus the square of the mean. Lemma 2.2 at lines 458–467 states
that, for two state-value functions in `[0, 1/(1−γ)]`, the state-action
supremum norm of the variance difference is at most
`4/(1−γ)` times the supremum norm of their difference.

## Verdict: PASS for the scoped lemma

`FiniteDistribution.variance` uses exactly the finite probability-weighted
first and second moments. Its centered-square identity proves nonnegativity;
neither fact is an assumed field. `DiscountedMDP.transitionVariance` applies
this variance to each actual transition probability row.

The final `transitionVariance_perturbation` theorem takes finite state/action
carriers and the source model `M` as typing/standing data. Its only value
hypotheses are the two pointwise source intervals. Expanding `M` reveals
normalized nonnegative transition rows, reward bounds and `0 ≤ γ < 1`; these
are source model assumptions, not hidden estimates. No proof step or target
conclusion appears as a hypothesis. It quantifies over all states and actions,
and the nested finite-Pi norm is the source's full maximum absolute-entry norm.
The constant and endpoints match. The proof uses a general absolute-value
perturbation inequality, which is stronger than required and then specializes
to the exact source intervals.

The module compiled with the pinned Lean version. Fresh `#print axioms` probes
of `variance_nonneg` and `transitionVariance_perturbation` reported only
`propext`, `Classical.choice`, and `Quot.sound`. This review does not claim
that the source inventory or the entire monograph is complete.
