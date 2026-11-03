# Finite occupancy builder handoff

Source: `source/upstream/tex/chapters/prelim.tex`, lines 748–763,
`eq:dh-pi-defn` and `eqn:defn-d1rho-finite`; SHA-256
`2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.

The implementation is `Formalization/MDP/FiniteOccupancy.lean`. `i : Fin
stages.length` corresponds to paper time `h = i + 1`. `stateAfter` iterates the
actual randomized policy and transition kernels over the preceding stages,
starting from an arbitrary finite probability distribution. The theorem
`stateAfter_expectation_eq_trajectory` identifies this recursively generated
law with the final-state marginal of the separately constructed finite path
law, mixed over initial states. `stateOccupancy_eq_trajectory_event` spells
out the corresponding state-event probability. `stateActionOccupancy` is the
probability of the state-action event obtained by sampling the current
one-step trajectory from that state law; `stateActionOccupancy_eq_trajectory_event`
spells this out as preceding trajectory followed by the current trajectory.
`stateActionOccupancy_eq` proves the source factorization, and
`stateOccupancy_first` proves `d_1 = ρ` for a nonempty episode. The index type
covers the last stage and makes the claims over decision times vacuous when
`H = 0`. No undefined terminal action is introduced.

Validation: `bash scripts/lean-local.sh Formalization/MDP/FiniteOccupancy.lean`
passed. A temporary copy with `#print axioms` for all five equivalence and
source-result theorems passed; each used only `propext`, `Classical.choice`,
and `Quot.sound`. Source SHA-256 is above; implementation SHA-256 is
`ad542b90fe2daeeaa93696f00fe763c7ca1e428042f769be7fd728c5657ab8d0`.
No source-level independent critic or facade/integration build was performed by
this builder. The later deterministic optimal-policy shorthand in the source
is not claimed here. The event equivalence uses a prefix trajectory followed
by a one-step trajectory; no separate equality to a single full-episode
trajectory event is asserted.
