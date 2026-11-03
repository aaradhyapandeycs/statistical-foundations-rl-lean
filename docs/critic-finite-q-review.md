# Independent review: finite-horizon action-conditioned returns

The lead reviewed this module separately from its builder, after reconstructing
the source from `chapters/prelim.tex:700–733, 784–799`. This is a scoped
ordinary source review, not an author-approved frozen-anchor audit.

The source conditions Q on the first state and action, then samples the next
state and later actions from their actual transition and policy laws. Its
terminal values are zero; for each nonterminal `h ≤ H`, it states the Q backup
and policy averaging equations together.

`actionTrajectoryLaw` is the product of the actual first transition and the
already-constructed future path law. It proves normalization rather than
assuming it. `trajectoryQ` is the expectation of the actual first reward plus
the path reward; it does not define Q to be a Bellman solution. The
`trajectoryValueAt` and `trajectoryQAt` suffix indices range over `Fin (H+1)`;
`Fin H` supplies every active time, with `castSucc` and `succ` providing the
current and next time. `trajectory_bellman_at` proves both source equations
for the same stage, state and action, and terminal lemmas prove both zeros.
The stage list stores actual nonstationary kernels, rewards and randomized
policies with the source probability and reward bounds. It adds no premise
that either Bellman equation holds.

The module compiled with pinned Lean. `#print axioms` for
`trajectory_bellman_at`, `trajectoryQAt_terminal`, and
`trajectoryValueAt_eq_backwardValue` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

This covers the stated policy Bellman equations in the implemented finite
trajectory model. An initial-distribution value, occupancy distributions,
common-environment policy comparisons, and an optimal deterministic policy
remain separate obligations. No result about infinite trajectories or the
whole paper follows from this module alone.
