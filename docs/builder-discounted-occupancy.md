# Discounted infinite-trajectory occupancy builder handoff

Source: `source/upstream/tex/chapters/prelim.tex` lines 145–175,
`eq:defn-dpi-occupancy-discounted-dist` and `eq:infinite-d-star-def`; source
SHA-256 `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
Staged file `.local/DiscountedOccupancy.lean`, SHA-256
`029a6c51d60dfd7e637ec212394354a7471afcfd1bbf9ddf03b432b9e0bf9606`.

For arbitrary normalized `ρ : FiniteDistribution State`, the construction
starts with the actual forward state law and actual joint event at each time
in a finite prefix of the stationary controlled trajectory. The results
`finitePrefix_pathState_eq` and `finitePrefix_pathAction_eq` prove those finite
prefix projections are exactly the source's `s_t` and `a_t` coordinates on
the original infinite path. `occupancyStateAt_eq_sourceEvent` and
`occupancyJointAt_eq_sourceEvent` then prove each timewise marginal is the
real probability of the corresponding event under `infiniteTrajectoryLaw π x`,
averaged over the actual initial distribution ρ. This uses the independently
proved finite/infinite prefix measure equality, not an assumed occupancy
relation. The initial mixture is represented explicitly as the finite
ρ-weighted expectation of point-initial probability laws; this file does not
package a separate measure on pairs `(s₀,path)`.

`discountedStateOccupancy_eq_source` and
`discountedJointOccupancy_eq_source` identify the defined geometric series
with exactly the source's infinite trajectory event formulas. Summability is
proved by the normalized timewise probability bound and `0 ≤ γ < 1`.
`discountedStateLaw` and `discountedJointLaw` package nonnegative, normalized
state and state-action occupancies as `FiniteDistribution`s.
`discountedJointOccupancy_eq` proves `d(s,a;ρ)=d(s;ρ)π(a|s)` by first proving
the corresponding actual finite-event factorization at each time and summing
it. `discountedJointOccupancy_sum_action` additionally gives the state
marginal. `discountedJointOccupancy_deterministic` proves the indicator
identity for **every** deterministic stationary point-mass policy; therefore
it can be specialized to the separately constructed stationary optimal greedy
policy once that module is integrated. No positivity of states/actions or
occupancy probabilities is assumed. At source endpoint `γ=0`, explicit
`discountedStateOccupancy_discount_zero` and
`discountedJointOccupancy_discount_zero` identify the initial state and
state-action laws.

Validation: `bash scripts/lean-local.sh .local/DiscountedOccupancy.lean`
passed. A temporary exact-source copy with twelve `#print axioms` commands
also compiled; checked were the two prefix-coordinate identities, two
source-event time marginals, two full source-series identities, the state and
joint probability distributions, joint factorization, deterministic indicator,
and two zero-discount boundary results. All used only `propext`,
`Classical.choice`, and `Quot.sound`. The probe was removed. Independent source
review, integration of the staged export and facade, and whole-project checks
remain for the lead. This does not claim any statistical lower bound or other
unrelated result.

Dependency hashes:

- `Formalization/MDP/OccupancyBridge.lean`: `e7c5519936dc6209640ab82da2aff2991bf71f2ee54f5f29d275ba11cd5a9ab5`
- `Formalization/MDP/PrefixValueBridge.lean`: `bd286567aa059c3e5fb293f1943eb06bd2e3d79c8dc9484d8a73195a2db16e89`
- `Formalization/MDP/InfiniteReturn.lean`: `0892b7c828e27835d4ee0f0ba48a5876bc26f05a92790da51f47df09e0730c8c`
- `Formalization/MDP/FinitePrefixBridge.lean`: `3ca9d38a8b1014054e83a318476b9fc4316573be5da3624cc20f70ccea87b6d7`
