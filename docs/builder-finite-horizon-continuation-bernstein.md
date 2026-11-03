# Bernstein concentration for actual empirical next-stage optimal values

Stable staged `.local/FiniteHorizonContinuationBernstein.lean`, SHA-256 `662944051f76f0d602356e43dfbad89c5a0568bf2110bf889f45ccae750663f6`.

Direct imports: staged `FiniteHorizonEmpiricalContinuation.lean` SHA `4cdf6cc568915df0ab34ff2fff63f025f851cbe8231ab888a73939b4a39c29dc` and production `Formalization.Probability.BernsteinFamily`. Its sampling dependency is SHA `c0e830fc8e3050ae0aadf8cfeec3c9d9209a72086d00a954ffa9e48024eb4e41`. Source context is the finite algorithm/backward-suffix decoupling at model-based chapter lines2526–2548 and the independently recorded plan `docs/source-finite-horizon-model-based-dependency-plan.md`.

## Six completed exports

`greedyStages_length` proves backward planning preserves the chronological episode length. `empiricalContinuationValue_bounds` proves actual empirical next-stage trajectory value is nonnegative and at most H−(h.val+1), the number of remaining decision stages. `empiricalContinuationValue_norm_le` derives the same supremum-norm bound. These are actual finite expected trajectory values, using the existing trajectory/backward bridge, not assumed value bounds.

`empiricalContinuationValue_code_row_bernstein` fixes an arbitrary strictly-future sample code and filler state, constructs the actual empirical optimal continuation through that code, and proves its exact fixed-row Bernstein success under the true current-row iid product law. This holds for every code, with no probability loss proportional to code cardinality. It is the explicit conditional slice: the current row is freshly distributed under its actual true-row product law while the future code is fixed.

`empiricalContinuationValue_row_bernstein` then proves for the actual full stage/state/action experiment, with strict probability greater than1−δ,

`|(P̂_h(s,a)−P_h(s,a)) V̂*_(h+1)| ≤ bernsteinRadius(P_h(s,a),N,1,δ,V̂*_(h+1))`.

The vector is the actual random empirical optimal next-stage trajectory value. The proof does not assume it independent: it builds a singleton family indexed by the finite future-data code, uses proved future-block/current-row independence, composes with the empirical-row function, proves actual row-law pushforward, and consumes `randomFamily_bernstein_success_gt`. The factorization theorem identifies the code value with the same full-data empirical continuation. Nonnegativity and all family/event measurability are discharged from actual trajectory bounds and the finite discrete code carrier. No fitted policy or realized vector is silently substituted into a fixed-test theorem.

`empiricalContinuationValue_row_bernstein_remaining` writes the exact radius as

`sqrt(2log(4/δ)/N) sqrt(Var_(P_h(s,a))(V̂*_(h+1))) + 2(H−h−1)log(4/δ)/(3N)`.

Only the linear norm term is bounded by remaining horizon. The variance is the true current transition row's variance of the actual same-data empirical continuation vector. There is no variance of a true value substituted or random empirical variance substituted without proof. Family cardinality is1, not the number of possible future codes, so the radius has no artificial exponential policy/code-count logarithm.

## Conditional meaning and exact scope

Both conditional-slice and mixed actual-law guarantees are supplied. The file does not define a particular version of a regular conditional probability or assert a new `condExp` indicator inequality; its joint probability result follows from independent-code mixing under the proved full experiment. This is the random-family mechanism needed for a finite-horizon concentration step. It should not be described as a literal conditional-expectation theorem absent an explicit further statement.

N>0 is the actual empirical-row domain; δ∈(0,1) is the concentration domain. h:Fin H is the current zero-based stage; the vector is after h (source next-stage index), and the remaining count is H−(h.val+1). The terminal-stage vector and its norm/variance/residual are zero and are covered. Zero true-row variance at earlier stages is also covered by the Bernstein linear term. Arbitrary nonstationary true kernels and known rewards in [0,1] are retained.

This is a **fixed-row** guarantee, not an already simultaneous all-stage/state/action event. It proves no H³ or H⁴ full policy-learning sample bound. Required next ingredients are a common row union event, tie-robust equivalence of empirical optimal suffix values, deterministic performance transfer, and sharp cumulative variance/simulation-error control. No independence of an arbitrary selected empirical policy is asserted. The external full-proof referral for `Thm:sample-compl-finite` remains separate from these independently proved prerequisites.

## Validation

Focused exact-source compilation succeeded against the isolated freshly built continuation/sampling artifacts and actual production/pinned dependencies. An exact-source-copy `.local/finite-horizon-build/ContinuationBernsteinAudit.lean` appended all six axiom probes; compilation exited0 without diagnostics and every export reported only `propext`, `Classical.choice`, `Quot.sound`. No admissions, custom axioms or target-shaped concentration assumptions occur. Dependency artifacts were preserved, and the compiler slot was released immediately after completion.

Pending independent source/semantic review, qualified production landing, actual export audit and project integration. No final finite-horizon theorem completion is claimed.
