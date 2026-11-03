# TD centered-square cross-state covariance review

Status: exact staged source reviewed, compiled, and axiom-probed. The module
remains quarantined under `.local`; no production Lean file was changed.

## Exact source and dependencies

| File | SHA-256 |
|---|---|
| `.local/TDSharpSquareCovarianceDraft.lean` | `0391af8b931384927f28fb9abcff12ba363deb245e01f099f521bcaf2e93db54` |
| `.local/TDSharpFreshVarianceBridgeDraft.lean` | `34686d029e51a1739ae0891095e4212208a56ac5693882a65afc401583d308cc` |
| `Formalization/ModelFree/TDCrossCovariance.lean` | `233cb669d3fb86f287ae7921e351d7896a2c0b4ab71f29280c3c991eec344544` |
| `Formalization/ModelFree/TDConditionalMoments.lean` | `82c1ad9cf6e8ae6f12173255af3ecbc29fd3c179334922073b80c010cfd45f7b` |
| Source `generative_model_model_free.tex` | `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22` |

The source target is Appendix C.2, `eq:TD-square-martingale` at source line 690,
with the relevant conditional-variance discussion at lines 2424–2432. It is
the centered-square martingale difference across distinct states, conditioned
on the samples used strictly before source update `k`. In this interface,
`1 ≤ k ≤ T`, `s ≠ r`, the sigma-field is
`tdPastSigma T (k-1)`, and the fresh observations are the actual array
coordinates `(s,k)` and `(r,k)`. Their laws are the two true policy rows
`M.policyTransition π s` and `M.policyTransition π r`. Zero-mass atoms are
allowed; there is no full-support condition.

## Proof reconstruction and review

The staged file defines the predictable square coefficient
`U_s(x)^2 - E_{P_s}[U_s(X)^2]`. It first establishes that the centered source
observation equals this coefficient selected by the actual fresh state, almost
surely. It then expands the product for `s` and `r` as a double sum over
`x,y`, multiplying the predictable coefficient product by the indicators at
the distinct coordinates `(s,k)` and `(r,k)`.

Each coefficient is measurable with respect to `tdPastSigma T (k-1)`, since
the pre-update iterate is predictable there. Conditional expectation pulls
that coefficient product out. The production theorem
`tdFreshIndicators_condExp_mul`, instantiated at `k-1`, supplies the exact
conditional indicator product mean
`P_s(x) P_r(y)` under the actual synchronous product law. The remaining
finite double sum factors into the product of each row's centered mean, hence
zero. The auxiliary centered-product identity allows distinct functions and
distinct row laws and assumes no atom positivity.

This derivation is square-specific. It does not infer a claim about squares
from `tdRowIncrement_condExp_cross` for raw TD noise. Centering the square
creates the terms `U_s^2 - E U_s^2` and `U_r^2 - E U_r^2`; the proof handles
their entire product by the double indicator expansion, including the
square-square and mixed centering terms.

The result supplies only the off-diagonal zero conditional covariance for
unpropagated centered-square observations. A subsequent weighted-row
conditional second-moment theorem still needs to assemble the diagonal
single-state bounds from the fresh-variance bridge and apply the actual
deterministic propagator coefficients. No Freedman bound, terminal variance
sum, or sharp TD probability theorem is claimed here.

## Fresh compile and axiom evidence

The exact source compiled to
`.local/td-square-covariance-audit/out/TDSharpSquareCovarianceDraft.olean`.
Its staged `TDSharpFreshVarianceBridgeDraft` dependency was taken from the
fresh isolated output recorded in
`docs/builder-td-square-fresh-variance-bridge.md`; the `TDCrossCovariance`
production dependency and pinned package artifacts were read from existing
build outputs. The pinned `.local/lean` was run with an isolated `LEAN_PATH`;
no package dependencies were rebuilt. The compile log is empty and the
command exited 0.

The separate `ImportAudit.lean` probes all six declarations in the staged
module. Every export depends only on `propext`, `Classical.choice`, and
`Quot.sound`; the import probe exited 0. The exact probe and `axioms.log` are
preserved in `.local/td-square-covariance-audit/`. The source contains no
`sorry`, `admit`, or custom axiom. This audit does not verify production
integration.

## Independent fresh-build confirmation (2026-11-03)

An independent fresh build was run from the exact staged source hash above,
using output directory `.local/td-square-covariance-independent-0391af8b/`.
The first invocation failed before elaboration because the isolated search path
omitted staged martingale and pairwise-variance dependencies; that failed
attempt is not counted as evidence. The successful rerun added these existing
staged dependency outputs to `LEAN_PATH`:

- `.local/td-square-fresh-variance-independent-review/`
- `.local/td-sharp-martingale-independent-review/`
- `.local/td-variance-pairwise-independent-review/`
- the project and pinned package Lean libraries.

The exact draft then compiled successfully with the pinned `.local/lean`.
`compile.log` is empty. The freshly emitted target artifact has SHA-256
`829070d40f5f0dc747e0ae2f2f76d635a69aec158dbf870f7a1a4aff4ca4776c`.
The independent import probe source has SHA-256
`c4715c91985712029a22db10a52e289155d7fe937452bfd50cbb6c828aefd1d4`; its
compiled artifact is
`2015c26685088a412f198c76dc60ea29be82f28b18ef84dfc04f5ca0603e1835`.
The probe covers the same six exports listed above, and independently reports
only `propext`, `Classical.choice`, and `Quot.sound` for each. A fresh scan of
the exact draft and probe source finds no `sorry`, `admit`, or custom `axiom`.

The successful build validates the draft module against its stated staged and
production imports. It does not promote the draft into the production module,
nor establish the downstream weighted-row/terminal-variance consumer described
above.

## Production integration

The reviewed square-specific cross-state covariance is integrated as `Formalization/ModelFree/TDSharpSquareCovariance.lean`. Declaration and proof bodies match the reviewed staged sources; imports and status comments were updated where needed. The full project check compiled 272 modules and audited 3,576 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
