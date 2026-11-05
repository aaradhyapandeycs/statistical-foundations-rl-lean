# Independent review: complete χ² support comparison

## Exact source identities

| File | SHA-256 |
|---|---|
| `QLearningChiComparisonDraft.lean` (private staged draft, not shipped) | `d92b11e3aa6ba74249ec3d18f83fb0bf73ff2829fc597f1b8c687ac6ec7620c0` |
| `QLearningChiLowerDraft.lean` (private staged draft, not shipped) | `7c3c610082d13523ac7f34f89dded65e96ba5e9eeb630ae200d7cea5aa35e4e8` |
| `QLearningChiUpperDraft.lean` (private staged draft, not shipped) | `a1a11cbd1debd8e26bd3bcedd0f13339cd0ae8858d7ab3f6823f23e33d7e2280` |
| `QLearningRobustComparatorDraft.lean` (private staged draft, not shipped) | `f4523b6f7400791447a3969c87be112c90f87c7eb64ba5a0ce9bbfc14ddfaa70` |

These exact hashes were rechecked immediately before the isolated fresh build. No production Lean source was modified.

## Source correspondence and scope

The target is all of source `lemma:Q-comparison-facts` (i),
`eq:Q-comparison-support`, in
`source/upstream/tex/chapters/generative_model_model_free.tex`, lines
1350–1359, with proof lines 2591–2635. The pinned chapter SHA-256 is
`7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.

For finite nonempty `State`, `qChiValueSpan v` is the finite maximum of `v`
plus the finite maximum of `−v`, i.e. `max(v)−min(v)`. The pairwise theorem
derives `|v(x)−v(y)|≤span` directly. The final theorem uses that pairwise
bound with the nominal finite probability row to obtain the centered bound
needed by the concrete lower-tilt witness. It does not substitute an
absolute-location bound such as `0≤v≤H`.

The wrapper proves expectation negation and variance invariance under
negation, derives upper and lower bounds for the actual feasible expectation
image, and proves
`sSup(expectations(−v)) = −sInf(expectations(v))` using `csSup`/`csInf` and
actual feasible distributions. Thus the infimum half is established without
assuming an optimizer or relying on an informal symmetry argument. The final
theorem combines this relation with the previously proved upper-radius result
and the affine-tilt lower witness for both signs. Its statement gives both
source inequalities for each of the supremum and infimum deviations.

The wrapper assumes finite nonempty `State`, actual `FiniteDistribution p`,
`ρ≥0`, `H>0`, and `span(v)≤H`. The source states `ρ>0` and
`H=1/(1−γ)` for `γ∈[0,1)`; the draft's zero-radius case is a valid extension.
The source max-minus-min premise is represented exactly by `qChiValueSpan`.
This is the full part-(i) comparison result at an abstract positive H. It does
not prove source part (ii), the robust-Q stability estimate, the Q-learning
sample-complexity theorem, or production integration.

## Independent isolated build and axiom probe

The exact-hash dependency closure compiled successfully bottom-up into
an isolated local audit directory (not shipped): RobustComparator, ChiUpper,
ChiLower, then ChiComparison. Existing project/package dependencies were
used; no dependency rebuild was requested. A separate import probe checked
all seven declarations in the comparison wrapper. Each reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The probe source is
`Probe.lean` (in an isolated local audit directory, not shipped).

This is independent evidence for the staged hashes above; the wrapper remains
quarantined and is not a production export.

## Production integration

The reviewed two-sided expectation comparison is now integrated as `Formalization/ModelFree/QLearningChiComparison.lean`. It proves part (i) of the source comparison lemma; part (ii) remains separate. The declaration and proof bodies match the reviewed staged source; imports or status comments were updated where required. The project-wide check compiled 250 modules and audited 3,333 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
