# Review: combined restricted lower-bound correction

The proposed correction is
`StatisticalRL.GenerativeLowerBound.sourcePolicyAndQ_risk_quarter_with_common_constant`
in [GenerativeLowerBoundCombinedRisk.lean](../Formalization/Generative/GenerativeLowerBoundCombinedRisk.lean).
It combines the two previously reviewed lower bounds with the common universal
sample constant `c_N = 1/32768`. It is a restricted replacement, not a proof of
Theorem 3.7 over its printed domain, and is not an author-approved erratum.

The hypotheses explicitly require `S ≥ 2`, `A ≥ 2`, and `SA ≥ 16`. The first
two do not both appear in the displayed theorem. The discount and accuracy
ranges agree with the source, and the sample condition is equivalent to
`N ≤ c_N log(SA)/((1−γ)^3 ε²)`. The result also handles `N = 0`, an extension
when samples are required to be positive.

Each clause fixes its estimator before choosing its own hard MDP; the two
witnesses may differ. The policy estimator may randomize its choice of a
deterministic stationary policy. The Q estimator may have an arbitrary
probability distribution over real Q arrays. Both risk events use actual
independent full-array samples and trajectory Q-values, with strict error
`> ε` and probability at least `1/4`. The finite carriers are the stated
canonical finite types; arbitrary-carrier relabeling is not asserted here.

An independent source/statement audit checked the final wrapper, including
quantifier order, the two observation/output laws, and the common-constant
arithmetic. The underlying results and their reviews are
[policy risk](critic-generative-lower-bound-kernel-quarter.md) and
[randomized Q risk](critic-generative-lower-bound-q-final-randomized.md).
The reviewed wrapper's SHA-256 is
`b09e11443edf778797d44bb592655a5d619b06af106650cd0c0a61a365bcdc7c`.
