# Independent source review: one-state lower-bound obstruction

The printed Theorem 3.7(ii) permits `S = 1`, `A = 16` through its displayed
condition `SA ≥ 16`. Under the monograph's stated information convention, its
universal Q-estimation claim is contradicted by an exact deterministic
estimator. The global preliminaries (`prelim.tex`, lines 42–43) and the
model-based chapter (lines 31–32) say rewards are known. The chapter's algorithm
inputs include the discount and reward table.

For the only state and each action, the estimator returns
`r(a) + γ max_b r(b)/(1−γ)`. It is a single fixed, measurable function of the
known reward and discount, and ignores the data. Every one-state transition
returns to the sole state, so this is the actual optimal forced-action
trajectory Q-value for every admissible one-state model. Its strict-error
event is empty under the actual product sampling law. Choosing `γ = 2/3`,
`N = 1`, and sufficiently small positive `ε` satisfies the printed
parameter restrictions for every proposed positive sample constant.

[Theorem37Negation.lean](../Formalization/Obstructions/Theorem37Negation.lean)
proves the negation of an encoded version of the claim. Its product experiment,
trajectory value, and parameter feasibility are established in
[OneStateExperiment.lean](../Formalization/Obstructions/OneStateExperiment.lean),
[OneStateTrajectory.lean](../Formalization/Obstructions/OneStateTrajectory.lean),
and [OneStateParameters.lean](../Formalization/Obstructions/OneStateParameters.lean).
Two independent source readers checked that this deterministic witness uses
only information available under the manuscript's conventions. No equivalence
between every conceivable randomized-estimator interface and the entire encoded
predicate is needed for this particular deterministic witness.

The theorem does not spell out a formal estimator signature, and prose about
large state and action spaces may indicate a narrower intended scope. Those
interpretive questions remain distinct from the displayed-domain example.
No author-approved correction has been obtained; restricting to `S ≥ 2`
excludes this example, but does not by itself establish the rest of the theorem.
