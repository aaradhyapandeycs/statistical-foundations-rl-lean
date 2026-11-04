# Independent review: fixed-policy cumulative variance

The reviewed source is `lem:cum-var-ub-Hsquare-ucbvi-mean`,
`chapters/onlineRL.tex:648–658`, in arXiv:2610.41903v1. The full chapter SHA-256 is
`393a4d26c228d833a27e54a4913489e499d2143f2f9b80ebf3c55d9a9ccb8c53`.

The deterministic policy is stage-dependent and selects a point-mass action.
Its actual finite path law samples the selected policy and each true
transition row. The recursive `finiteTrajectoryVarianceSum` adds the true
row variance of that same policy's suffix trajectory value at every actual
state/action; the terminal value is zero. No empirical row, independent-copy
substitution or algorithm optimism is used.

The one-step return-variance decomposition retains action variation and the
expected tail-return variance. Induction bounds cumulative transition variance
by total return variance; rewards in [0,1] bound the return in [0,H], giving H².
The intermediate theorem even permits randomized fixed policies. The source
specialization is deterministic and pointwise in the initial state. The
statement-index proof averages that stronger export over an arbitrary initial
distribution, so the printed expectation claim follows without a source
correction or extra hypothesis.

Independent review checked source correspondence, the byte-preserved moved
definition and its namespace/Fintype context, the seven qualified modules,
and the actual `StatisticalRL.Statements.Lemma5_4_holds` proof. Focused probes
and the affected whole-library audit permit only `propext`, `Classical.choice`
and `Quot.sound`. See the linked verification report for exact build scope.

This certifies the fixed-policy expected variance lemma. Adaptive conditional
budgets, high-probability cumulative bounds and the final regret theorem need
separate proofs and are not established by this release.
