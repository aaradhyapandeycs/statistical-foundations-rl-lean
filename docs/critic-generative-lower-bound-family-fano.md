# Independent review: corrected family Fano instantiation

**Scope:** source-level review of the staged finite Fano decision and its
indexed-family specialization. At the time of this source review I did not
run Lean. The subsequent independent exact-source audit in
`critic-generative-lower-bound-fano-risk-fresh-audit.md` compiled the
30-module Fano/risk closure and probed all recognized declarations.

## Reviewed sources

- `.local/GenerativeLowerBoundJointDecision.lean`, SHA-256
  `2540aec8fe16986434671c61d77457444013084c633e986c69e464187c2b67e7`.
- `.local/GenerativeLowerBoundFamilyFano.lean`, SHA-256
  `eb5e5ab951475905a55a0be518a5a7403bbb03397e2583c3aea3d6de631935d8`.
- Supporting definitions inspected: `FamilyObservation`
  (`6da8556ccf586ae09e25df581059f7e09acaf556984812c1c68c0a8ff11d62b0`),
  `FamilyKL` (`e9a533f2ce8672b52af16b311f7e618910140e7c64090c61194fcd596198905e`),
  `FamilySparseKL` (`6f7d77cf86d1a315994d441180c1221a548590e2c424173d12e59773dab58145`),
  and `IndexGeometry` (`e76ba0b8fc41c0da17b0c643f2db1175cc2135f48b2b4e293a5d978916eef8b0`).

## Findings

The decision argument has the expected orientation and event. It constructs
actual uniform-prior joint laws, uses the event `d x = i` for one common
decoder, and compares the joint law with the product of the uniform index and
baseline `Q`. Under that reference law exactly one of the `K` indices matches
`d x` for each observation, so the success-event mass is exactly `1/K`. The
joint KL identity is the average of `KL(P_i || Q)`, in the same first-to-second
orientation. The complement step gives average error, including the endpoint
cases through probability complements.

The generic decision theorem requires full atom support for every `P_i` and
for `Q`. This is valid for the family only on the active-coordinate space:
the parameters satisfy `0 < p ≤ q < 1`, and each indexed Bernoulli product has
positive mass at every Boolean vector. It would be false on the reconstructed
full-array space, whose absorber rows and restricted transition outcomes are
deterministic. The specialization correctly applies Fano before reconstruction.

For any actual full-array decoder `d`, the active decoder is the same function
composed with the model-independent `familyReconstruct`. The actual family law
is the pushforward of the active product law. The displayed `Measure.map_apply`
therefore identifies the active event `{x | d (familyReconstruct x) ≠ i}` with
the actual event `{data | d data ≠ i}` for every hypothesis. No hypothesis-
dependent decoder is introduced.

The KL transfer is likewise correctly oriented: the actual
`KL(samplingLaw_i || samplingLaw_none)` equals active
`KL(P_i || P_none)`. The baseline `none` term is zero; every `some (j,k)` term
is bounded by `1024 * N * (1-γ)^3 * ε^2`. Bounding the mean by this same upper
bound (rather than exploiting the baseline zero for a sharper factor) is
valid. The exact hypothesis cardinality is `K = 1 + m*n`; `m,n ≥ 1` ensures
`K ≥ 2` and hence `log K > 0`. The argument also covers `N = 0`.

## Scope and caveats

This establishes the stated average decoder-error Fano ingredient for the
corrected indexed family, conditional on its source parameter lemmas. It does
not by itself establish a policy-risk lower bound, the strict numerical
`> 0.1` conclusion, or the sample-threshold arithmetic; these require the
separate decoder-to-risk reduction and corrected source assumptions. In
particular, the proposed correction in `critic-theorem37-correction.md` is not
an author-approved replacement for the disputed printed theorem. The
builder-reported axiom list is `propext`, `Classical.choice`, and `Quot.sound`
for the two principal exports, but this review did not rerun `#print axioms`.

**Verdict:** no source-level mathematical defect found in these two staged
Fano ingredients. Their staged exact-source compile and standard-only axiom
evidence are now independently recorded in
`critic-generative-lower-bound-fano-risk-fresh-audit.md`; production
qualified-import validation remains outstanding.

Production integration: the relevant production module bodies match the independently reviewed staged sources, with qualified imports where needed. The complete project build compiled the actual exports and audited 2,279 declarations, permitting only `propext`, `Classical.choice`, and `Quot.sound`.
