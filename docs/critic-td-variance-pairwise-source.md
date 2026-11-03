# Source review: finite pairwise variance helper for the TD square bound

## Bound scope

Reviewed `.local/TDVariancePairwiseDraft.lean`, SHA-256
`eddac49017762311a11b0f86590414c8d21ed6279cff2d7b0df2b792c5bea022`,
against the source chapter
`source/upstream/tex/chapters/generative_model_model_free.tex`, SHA-256
`7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.
The source requirement is the scalar inequality in the TD variance-proxy
proof, lines 2423–2432, used for the actual fresh-row value at a fixed state.
This is a source-level review only; no compiler was used.

## Fidelity and endpoint review

The helper proves the pairwise representation

`Var_d(f) = (1/2) Σ_x Σ_y d(x)d(y)(f(x)-f(y))²`

for every finite probability law, then applies it to `U` and `U²`. Under
`0≤U(x)≤H`, it obtains `|U(x)|≤H` and the pointwise factorization
`|U(x)²-U(y)²| = |U(x)-U(y)| |U(x)+U(y)| ≤ 2H |U(x)-U(y)|`.
Squaring and weighting by the nonnegative product probabilities preserves
this bound. The common factor `1/2` cancels, giving exactly
`Var(U²)≤4H² Var(U)`. The factor 4 is the source constant; there is no loss
or missing factor in the pairwise argument.

The boundary cases are included. The double sum includes all carrier points,
including zero-probability atoms, without dividing by probabilities or making
a support assumption. A singleton carrier has only zero pairwise
 differences, so both variances vanish. If `H=0`, the premise forces every
`U(x)=0`; the result is `0≤0`. The helper carries `_hH : 0≤H` but does not
use it; that premise is redundant for the inequality as stated because the
pointwise interval hypothesis is already explicit. It is harmless and agrees
with the source's `H=1/(1-γ)>0` application.

This helper matches the source's use with `H=1/(1-γ)` and an actual
conditional fresh-row distribution, provided the consumer supplies the
source's actual iterate bounds `0≤U≤H`. It proves only the finite-law
scalar square-variance inequality and the pairwise identity. It does not by
itself identify a TD conditional expectation with a transition-row law,
prove the fresh-update affine variance identity, handle cross-state
covariances, or establish a terminal propagated variance bound. Those are
separate consumer obligations in the TD draft chain. No source completion is
claimed from this helper alone.

## Review disposition

The mathematical statement and exact constant are source-faithful for the
finite-law step at lines 2423–2432. The zero-mass and degenerate cases are
safe. This review does not certify elaboration or transitive axioms; the
builder note reports a prior exact-source compile and probe, which should be
independently rebuilt before landing if required by the integration gate.

## Independent fresh build and axiom probe

The reviewed exact SHA was copied to
`.local/td-variance-pairwise-independent-review/TDVariancePairwiseDraft.lean`
and freshly compiled to the same directory with exit 0 and an empty compile
log. The fresh `.olean` SHA-256 is
`a35c1edc61c234c05af49251afa0a2c5d369d10f5ca7a520ad8c19257233e611`.
A fresh isolated import audit copied from the earlier concrete-edge-case
probe compiled successfully; its source SHA is
`47419f2c3e93e051be8f748b3fe3a9ee25da6009d15eca1dc3308bed5d2ab3c3`,
output `.olean` SHA
`58b01050d8efa21c87f9f6d17311cd4cf2b023dab6b1ae8380811acf6df32101`,
and axiom-output SHA
`4931d1065b68ee09efcfa61e60fbd3e72340efff0839b11495a3c371dab7061c`.
The audit probes the three exports and includes concrete Bool-with-zero-atom,
singleton, and `H=0` applications. All three exports report only
`[propext, Classical.choice, Quot.sound]`. This independently verifies the
finite helper, not the separate actual-TD conditional-law bridge.

## Production integration

The reviewed finite-law variance identity and square-variance inequality are now integrated as `Formalization/ModelFree/TDVariancePairwise.lean`. The actual TD conditional and cross-state bridges remain separate. Declaration and proof bodies match the reviewed staged source; imports and status comments were updated where required. The complete project check compiled 263 modules and audited 3,454 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
