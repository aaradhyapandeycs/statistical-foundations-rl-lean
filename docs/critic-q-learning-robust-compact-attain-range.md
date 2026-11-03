# Independent source review: robust χ² compactness, attainment, and range

## Reviewed source identities

This review is bound to the following exact staged files:

| File | SHA-256 |
|---|---|
| `.local/QLearningRobustBallCompactDraft.lean` | `f9f725a6e9601e1bd7383d039591fd6a57d4292af53fbfefc0d3e7ad3ac18708` |
| `.local/QLearningRobustAttainmentDraft.lean` | `351714a982da4b21d279a17314c9cb6a5fb00791105fae7464a7fa5a51307d82` |
| `.local/QLearningRobustRangeDraft.lean` | `644cad4fae188e7cae10cd8ddcfe8b8ea6e0dd2447f6a9e4b76579df3196dc7b` |
| `.local/QLearningRobustComparatorDraft.lean` | `f4523b6f7400791447a3969c87be112c90f87c7eb64ba5a0ce9bbfc14ddfaa70` |
| `.local/QLearningRobustContractionDraft.lean` | `91de4ee4c14cb9a9f9d90bea6381bb8aadeadbc8ea348c4e1f39568568b7a574` |

The five hashes agree with `docs/builder-q-learning-robust-range.md` at review time. The source/semantic review was followed by an independent hash check, fresh isolated compile, and axiom probe; no production integration is implied.

## Findings

The compactness construction models a row by real coordinates with nonnegativity, total mass one, explicit zero-mass constraints wherever the nominal row has zero mass, and the finite χ² sum only over positive nominal coordinates. The denominator is therefore fixed and nonzero on every included summand. The equivalence theorem reconstructs an actual `FiniteDistribution` and identifies its probability function with the coordinate vector. The compactness argument places this closed set inside the finite-dimensional coordinate cube `[0,1]`; the upper coordinate bound follows from nonnegativity and total mass one. Continuous linear expectation then attains both extrema, and the bridge file transfers those optimizers to the expectation image used in the robust Bellman operators.

The range construction chooses the maximizing feasible row at the upper robust fixed point and, independently, the minimizing feasible row at the lower robust fixed point. These rows are assembled into actual finite transition kernels while preserving the original reward and discount. The source extrema equal the selected row expectations, so the shifted robust fixed points satisfy the ordinary optimality fixed-point equations of the constructed MDPs. The existing optimality fixed-point range theorem supplies the shifted `[0,H]` bounds. Taking action maxima yields the stated pairwise state-value bound `|V(s)-V(t)| ≤ H`, without claiming that the unshifted robust values lie in `[0,H]`.

## Scope and caveats

- These declarations require only `ρ ≥ 0`; the source comparison application uses `ρ > 0`. This is a valid extension for the stated deterministic compactness/range facts, but the source-selected radius must still separately be shown positive when applying the source result.
- The range theorem is parameterized by arbitrary real `b`; it does not establish the source-derived formula or sign of `b`. Those facts must come from the source-specific construction.
- The files do not prove the χ² support/stability estimates, a sharp robust-Q perturbation bound, residual absorption, a stochastic event, or a sample-complexity theorem.
- The staged headers still describe the compactness, attainment, and range files as “uncompiled” drafts. Per the builder handoff, compilation was reported successful; the comments should be corrected when those modules are deliberately landed, without changing theorem statements.
- This review found no source-level mismatch in the compactness-to-attainment-to-selected-model range chain. The independent rebuild and axiom probes are recorded below.

## Independent isolated build and axiom evidence

All five hash-pinned files in the table compiled in dependency order into `.local/robust-range-independent-audit/`, using the project's existing compiled dependencies and no dependency rebuild. The build command pattern was:

```text
LEAN_PATH="$PWD/.local/robust-range-independent-audit:$(lake env printenv LEAN_PATH)" .local/lean -o .local/robust-range-independent-audit/<Module>.olean .local/<Module>.lean
```

The order was Comparator, Contraction, BallCompact, Attainment, Range. A separate probe imported the isolated Range output and ran `#print axioms` for all 9 BallCompact declarations, both Attainment declarations, and all 17 Range declarations (28 total). Every declaration reported exactly `propext`, `Classical.choice`, and `Quot.sound`; no custom axiom or unfinished proof appeared. The probe is `.local/robust-range-independent-audit/Probe.lean`. The earlier source caveats remain unchanged.

## Production integration

The reviewed compactness, attainment and range results are now integrated as `Formalization/ModelFree/QLearningRobustBallCompact.lean`, `QLearningRobustAttainment.lean`, and `QLearningRobustRange.lean`. The declaration and proof bodies match the reviewed sources; imports and source-status comments were qualified or updated. The complete project check compiled 245 modules and audited 3,277 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`. The scope and remaining obligations described above remain in force.
