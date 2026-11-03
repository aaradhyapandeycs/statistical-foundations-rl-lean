# Independent source review: Q-mixture observation and row moments

Reviewed exact staged revisions named by `docs/builder-generative-lower-bound-q-observation-moments.md`:

| Module | SHA-256 |
|---|---|
| `.local/GenerativeLowerBoundQMixtureObservation.lean` | `ca5198f6e8f1742a2c666ca52cda2eb6701c1eb9abd75f22c8c2372862b152af` |
| `.local/GenerativeLowerBoundQMixtureMoment.lean` | `ca8c6185fb151e474b5596f2bf5c9e9bf286191b0589df48d743a2e52eff1101` |
| `.local/GenerativeLowerBoundQMixtureLikelihood.lean` | `a6bb4a78fc454d4e2bf0ef223e4e55bea8faaa79a253f5efdf96b98ccafaf1b8` |
| `.local/GenerativeLowerBoundQMixtureRowMoments.lean` | `7f5df8bfb9c72f24c7624ac1f061dcf46db30b250708532fbcf76ef0cbe9c6c8` |

This is an independent source/semantic review only. The builder handoff reports successful compiles and standard-only axioms for selected results; this review did not run Lean or reproduce those checks.

## Actual observation law

The encoded coordinates are exactly active state/action/sample triples `((Fin m × Fin A) × Fin N)`. Each Boolean is whether the corresponding actual transition sample self-loops. Under the one-row family, its parameter is q on the designated row and p on all other rows. Independence follows by restricting the actual product sampling law to the injectively selected active coordinates. The full-array reconstruction fills absorber coordinates with `none` and each active coordinate from its Boolean; the separately proved row-support property makes reconstruction after encoding equal to the actual complete array almost surely. Thus the law identity correctly includes deterministic absorber rows and is stronger than an active marginal calculation.

No positive sample-size condition is required: at `N=0`, the active-coordinate index and the complete sample index are empty, the product law is the empty product, and the full-array reconstruction still identifies the unique empty-coordinate array. The MDP interface requires `[NeZero A]`; p≤q<1 supplies valid transition parameters in these theorems. No positive m is needed for the sampling-law identity itself because an empty active state set is meaningful.

## Scalar and row likelihood moments

For a baseline Bernoulli(p) draw, the likelihood ratio is q/p on `true` and (1−q)/(1−p) on `false`. The scalar identity simplifies its squared mean to `1+(q−p)²/(p(1−p))`, assuming only `0<p<1` for nonzero denominators. Under the actual baseline atom masses p and 1−p, the first moment is one and the squared moment has that same value. Independence across the N samples then gives the actual baseline row second moment as the Nth power of the scalar factor. At N=0 both the row likelihood and its squared moment are 1, matching exponent zero.

The row-moment statements carry `q≤1`, appropriate for q to be a Bernoulli parameter, though the builder notes this hypothesis is unused in some scalar integral proofs. The actual Q-mixture family further has p≤q<1. The likelihood definitions divide only by p and 1−p; their assumptions guarantee both are strictly positive. The row results alone do not identify a Radon–Nikodym derivative on the full law.

## Scope and limitations

The staged `qMixtureLikelihood` definition averages over `m*A` alternatives, so using it as a probability-mixture likelihood requires `m>0` and `A>0`; the current definition itself does not impose those hypotheses, and for a zero dimension its real denominator is zero. The reviewed observation and one-row moment theorems do not use that uniform-mixture definition, and are not invalidated by this edge case, but every downstream theorem using the mixture must provide nonempty dimensions. The handoff correctly leaves exact full-law RN identification, different-row cross moments, mixture χ²/testing, estimator risk, and a final statistical conclusion open.

**Verdict:** the full-array reconstruction and the Bernoulli scalar/row moments match the stated actual laws, including N=0. The current exports establish a diagonal single-row moment only, not the cross-row or mixture moment needed for testing. Any use of the uniform mixture likelihood additionally needs positive dimensions.

Production integration: the corresponding production module bodies match the independently reviewed staged sources, with qualified imports. The full project export compiled and audited 2,522 declarations, permitting only `propext`, `Classical.choice`, and `Quot.sound`.
