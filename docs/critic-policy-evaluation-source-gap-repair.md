# Independent review: policy-evaluation sample-gap repair

## Verdict

The integrated all-state result has the right source-facing radius, data law, and quantifiers. It proves the radius event for every positive sample count, which fills the gap between the sample threshold used in the recursive concentration proof and the weaker threshold on the manuscript's final displayed radius. The deterministic low-sample argument does not retroactively validate intermediate recursion inequalities outside their stated range, and this radius result alone is not the complete sample-complexity theorem.

## Result reviewed

For a finite nonempty discounted MDP, a fixed stationary policy `π`, a positive natural sample count `N`, confidence `0 < δ < 1`, and a source constant `C₀ ≥ 8`, the integrated theorem proves

`1 − δ < P_{samplingLaw M π N}(‖valueEstimator M π N − M.trajectoryExpectedValue π‖∞ ≤ 3 √(8 C₀ log(S m / δ) / ((1 − γ)^3 N)))`,

where `S` is the state count and `m = ⌈log(e/(1−γ))⌉`. The estimator is the actual empirical-model policy-evaluation estimator; the target is the true infinite-horizon trajectory value for the same fixed policy. The probability law is the actual product generative experiment, with independent samples from the policy-averaged transition row at each state. No data-selected policy is involved.

The confidence inequality is strict, as in the source's “exceeding `1−δ`” statement. The theorem includes zero discount. The MDP structure provides nonempty state and action carriers; no empty-carrier case is being added.

## Why the sample gap closes

The argument first proves the API-radius result for every `N > 0`. At low sample counts, both the empirical and true policy values lie in `[0, 1/(1−γ)]`. Their sup-norm difference is therefore at most `1/(1−γ)`, which is below the target radius on the low-count branch. This branch is pathwise, so its event has probability one.

Above the branch cutoff, the proof invokes the existing high-sample actual-law result. The cutoffs overlap: the deterministic branch covers `N ≤ 72 β/(1−γ)`, while the high-sample result needs `N ≥ 64 β/(1−γ)`. Thus no sample count is omitted, including the cutoff equality.

For at least two states, the API logarithm is bounded by `8 log(Sm/δ)`. Taking `C₀ ≥ 8` makes the API-radius event a subset of the manuscript-radius event without changing the law or confidence. For one state, the empirical and true policy values agree exactly for every sample, so the target event is universal. These branches cover every finite nonempty state space.

## Scope and limits

The manuscript's final radius statement uses `β₁=C₀ log(Sm/δ)` and assumes `N ≥ β₁/(1−γ)`. Its preceding recursive proof uses a stronger sample-size condition for an intermediate bound. The reviewed result extends the **final radius event** to all `N>0` by the deterministic range argument. It does not claim that the stronger intermediate inequalities hold at small `N`.

The result has no `ε` or sample-budget binder. The separate conversion from the printed sample budget to an `ε` guarantee, and validation of every earlier recursive concentration step, remain distinct claims. `C₀ ≥ 8` is a sufficient explicit choice for this beta comparison; the manuscript leaves its universal constant unspecified. This review does not certify that a particular value satisfies every other use of `C₀` in a full theorem.

## Integrated source identity

The exact integrated declarations reviewed are:

- `valueEstimator_all_positive_samples_source_radius` — SHA-256 `5c19f2cd35cf1d899012c5600ab8430c13420e428d609b15b632a83b5718bdce`
- `policyEvaluationBeta_le_eight_source_log` and its event-inclusion helper — SHA-256 `76cf9d13e21749e6f522f0dc7f27ae91031437be22862f513f8ba4c9c772e709`
- `policyEvaluation_source_radius_all_positive_samples` — SHA-256 `394edbd514d77c7e23dbe173a958644cf2b38f7d6560bacdfc2647918c5f86e9`
- `policyEvaluation_source_radius_all_states_positive_samples` — SHA-256 `7db49509d0bf370f198709bb89124920dbe457739379323d9f4f7233509039bd`

Their substantive theorem bodies match the independently reviewed candidate statements and proofs; the migration differences are module-qualified imports and introductory comments. The earlier independent reviews approved the all-positive branch arithmetic, beta comparison, event inclusion, and one-state exactness. The source theorem being repaired is the policy-evaluation radius at the end of the generative-model policy-evaluation proof (equation `ice-cream` and its following paragraph, approximately lines 628–634 of the chapter source).

This note is an independent source/semantic review of the integrated text. It makes **no claim** about a fresh build or exported axioms; those require separate recorded validation evidence for these exact integrated hashes.
