# Independent review: robust χ² policy value and singleton-action bridge

## Scope

This review covers the integrated module
`Formalization/RobustRL/ChiSquaredPolicyValue.lean`, source SHA-256
`1d52fd66af57d066f1c5bceac71054265e4e363661bebc1799b4d69dc0399dbf`.
Its production-layout preview was source-reviewed, compiled in an isolated
output against existing project dependencies, and its declarations were
axiom-probed. The working project and a separate clean copy also passed the full module
build and axiom audit on matching source hashes. This is not a proof of the
full lower-bound theorem.

## Mathematical correspondence

The candidate represents a robust MDP by a nominal discounted finite MDP and a
strictly positive radius. An admissible adversary is one complete transition
kernel whose every state-action row belongs to the support-aware finite χ²
ball. This matches the source's rectangular row-wise uncertainty set and the
direction `χ²(candidate row ∥ nominal row)`. Candidate mass is required to be
zero on every nominal zero-mass state, matching the absolute-continuity
condition in `source/upstream/tex/chapters/intro.tex`.

For a fixed stationary randomized policy, the candidate set consists of the
actual infinite discounted trajectory expectations under those feasible
kernels, with the nominal reward and discount unchanged. The robust policy
value is the infimum of that set. Nominal-kernel feasibility proves the set is
nonempty, and the trajectory-value bounds place its infimum in
`[0, 1/(1−γ)]`. The value from an initial distribution is the finite
expectation of the statewise robust values, consistent with
`source/upstream/tex/chapters/prelim.tex`'s trajectory-value definition and
`source/upstream/tex/chapters/robust_RL.tex`'s robust-value definition.

The policy carrier is specifically `StationaryPolicy State Action`. The
candidate's optimal benchmark is therefore a supremum over stationary
randomized policies; general robust optimal-policy attainment is not proved.
When the action carrier is a subsingleton, every action distribution is equal,
so every stationary policy has the same robust initial-distribution value.
The candidate proves that this value attains the stationary supremum, that the
suboptimality gap is zero, and that for every positive ε the strict failure
event is empty. Its measure is consequently zero under any data law.

The singleton result is a domain obstruction only when an external theorem
claims a positive failure probability on that action domain. It does not
construct the source lower-bound model family or sample experiment, and does
not establish Theorem 7.5. The source theorem's wider policy quantifier also
requires care: this candidate API covers stationary randomized policies, not
arbitrary history-dependent policies.

## Build and axiom evidence

The exact production-layout source compiled successfully in isolation against
the current project dependency artifacts. The 21 checked declarations and
structure projections use only `propext`, `Classical.choice`, and `Quot.sound`;
no custom axiom or `sorryAx` was reported. The only compiler diagnostic was a
non-fatal unused-section-variable warning. The isolated check did not rebuild the transitive project dependency closure;
that is covered separately by project-wide verification.

## Review conclusion

The finite χ² orientation/support condition and actual-trajectory infimum are
consistent with the cited source definitions. The singleton-action equality,
attainment, zero gap, and empty strict-error event follow within the stated
stationary-policy API. General policy semantics, robust optimality for
non-singleton actions, source experiment construction, and the full lower-bound
argument remain outside this result.
