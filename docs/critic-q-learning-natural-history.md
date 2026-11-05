# Independent review: Q-learning natural-history bridge

## Exact sources audited

The current staged sources do not match the older hashes in `builder-q-learning-natural-history.md`:

- `QLearningNaturalHistoryDraft.lean` (private staged draft, not shipped): `841361faa2ba6d092b6f46ccb15e0bcda03d591e147f74b1f6d611de334b7ffd`.
- `QLearningHistoryAdaptationDraft.lean` (private staged draft, not shipped): `766309449c858a91456f82499c75e4de9c2af11fc8d6268f37f4e59815562c4f`.

I independently compiled the current exact sources and their ten staged dependencies in dependency order to an isolated local audit directory (not shipped). The build completed successfully. An import-only probe checked all nine public declarations from the two target modules; every declaration reported only `propext`, `Classical.choice`, and `Quot.sound`. There were three benign linter warnings in upstream Q-learning modules (unused section instances and an unused simp argument); no errors or admissions.

## Source and semantic findings

`qPaddedIncrement` agrees with the actual Q-learning row increment for `t < T` and is definitionally zero otherwise. Thus the time-indexed increment process has exactly T potentially nonzero draws; for T=0 every increment is zero.

`qPastSigma_mono` factors the shorter prefix code through the longer one using the canonical restriction map. In the adaptation bridge, increment j is shown to depend only on the completed prefix through layer j: the iterate is used through update j−1 and the fresh row sample at layer j is included. For j≥T the padded increment is zero. This yields strong measurability under `qPastSigma T (j+1)` and the inclusion

`priorIncrementSigma (qPaddedIncrement ...) t ≤ qPastSigma T t`.

The centering theorem then applies the generic conditional-expectation tower step from the actual sample-prefix sigma algebra to the smaller increment-generated history when `t < T`. When `t ≥ T`, it uses the zero-padded increment and `condExp_zero`. This includes T=0 without requiring a current coordinate.

For the squared increment at `t < T`, the tower identity is correctly stated with the right side equal to the conditional expectation of `qRowVariance` under the smaller history. It does not simplify that conditional expectation to the row variance itself. A deterministic variance cap or Freedman conclusion is not proved here.

The bridges use the actual `qSamplingLaw` and the earlier prefix conditional-centering/variance identities. The source does not assume the desired natural-history centering or variance identity as a premise. No source-level issue found in these statements or their zero-padding conventions.

## Scope

This evidence is for the exact staged closure only. Production imports, production export axioms, deterministic variance domination, and any concentration/rate result remain separate checks.

Production integration: reviewed source declarations and proofs compile under production module names; staged imports and stale staging-only comments were updated. The complete project export compiled and audited 2,863 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
