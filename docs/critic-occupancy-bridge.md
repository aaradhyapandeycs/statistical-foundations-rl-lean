# Independent review: full-episode occupancy bridge

The lead reviewed the source and code independently of the builder. The
source target is `prelim.tex:749–774`: state and state-action event
probabilities at each genuine time of a single trajectory starting from ρ,
their factorization, and its specialization to an optimal deterministic policy.

## Verdict: PASS for the stated bridge

`pathState` reads the state before each action and `pathAction` reads the
corresponding action directly from the complete `FinitePath`. Both are indexed
by `Fin H`, so no nonexistent decision is manufactured when `H = 0`.
`fullPath_state_expectation` and `fullPath_joint_expectation` use the actual
full `trajectoryLaw`, average over the actual initial distribution, and
inductively marginalize the remaining path through the proved expectation
and normalization laws. They hold for arbitrary real test functions. The two
event theorems apply these equalities to indicators and recover the previously
defined state and joint occupancy probabilities. There is no positivity or
division hypothesis for individual state-action events.

For the optimal specialization, `greedyIndex` carries the same decision index
through the length-preserving greedy construction, `greedyActionAt` refers to
the actual current environment and its optimal continuation, and
`greedyStages_policy_at` proves that the selected policy is the corresponding
point mass. `greedy_stateActionOccupancy` derives the indicator formula from
the actual generic factorization. The source's optimal-policy status rests on
the separately reviewed `FiniteOptimal.lean` results; it is not assumed in
this theorem.

Binders are the source finite carriers, stagewise kernels/rewards/policies,
initial distribution, valid index, and arbitrary state/action or test
function. Their probability normalization and reward conditions are model
fields, not extra conclusions. No missing event identity or optimality result
is bundled as a premise. Independent rechecking of the complete import
closure is provided by the project integration audit.

Reviewed implementation SHA-256:
`e7c5519936dc6209640ab82da2aff2991bf71f2ee54f5f29d275ba11cd5a9ab5`.
Source `prelim.tex` SHA-256:
`2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
The existing finite optimality review records the total-policy/zero-horizon
representation limitations; this review does not certify the entire chapter.
