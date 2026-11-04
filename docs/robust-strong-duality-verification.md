# Robust-RL strong duality: full Lemma 7.1 verification

Both the TV and chi-squared bullets of `lemma:dual-form`,
`chapters/robust_RL.tex:302–324`, are proved. The surrounding source assumes
`σ > 0` at lines 31–32. The monograph and every chapter remain incomplete.

## Statement and proof

`StatisticalRL.Statements.Ch7.Lemma7_1` expands both actual feasible-row sets,
their primal infima, the two clipped finite-sum objectives, the global
all-state minimum/maximum interval, and an attained value dominating every
other interval point. The source hypotheses are finite nonempty state space,
a normalized nominal row, `V ≥ 0`, and `σ > 0`. There is no optimizer, root,
radius-case, witness-feasibility, or payoff premise. No `DecidableEq` premise
is added. The existing TV projection and proof remain available unchanged.

The chi-squared set forces zero mass wherever the nominal row is zero and
sums `(q(s)-p(s))²/p(s)` over positive nominal atoms. This has the source
orientation and no division by a zero nominal atom. The proof covers arbitrary
positive radius, ties, singleton carriers, zero variance, and zero nominal
atoms, including those outside the supported value range.

The chi-squared witness is constructed in four exhaustive cases: sufficiently
large radius concentrates on the lowest supported level; zero variance uses
the nominal row; the small-radius endpoint uses a feasible affine density;
the remaining case derives an interior clipped-moment root by continuity and
the intermediate value theorem. Every case supplies an actual feasible row
whose payoff equals the scalar objective. The existing weak inequality gives
the primal equality and interval-wide maximum dominance. The wrapper derives
the expanded statement from these exports and the TV export; it only proves
representation/endpoint bridges.

The main new export is
`StatisticalRL.RobustRL.ChiSquaredSourceMaximum.chiSquared_source_maximum`;
the combined proof is `StatisticalRL.Statements.Ch7.Lemma7_1_holds`.
See the [independent source and consumption review](critic-robust-strong-duality.md).

## Exact build evidence

Canonical run `20261104T054840741272Z` passed: **13 rebuilt
modules + 434 unchanged reused modules = 447 current project modules**.
The full facade and `Audit.lean` were rebuilt. The transitive namespace audit
passed **5,026 project declarations**, allowing only `propext`,
`Classical.choice`, and `Quot.sound`. The integrated actual-export probe also
passed for the chi-squared maximum, both Chapter 7 proofs and statement.

This was an affected rebuild, **not a fresh 447-module clean build**. Its
verified baseline is the published TV438 tree, manifest SHA-256
`003ee94561cb5b2ee202a53e915498df09421e940f37fcdc1badef10499fdfb3`,
which itself rebuilt 23 modules and reused 415 from the successful clean
418-module TD check, manifest SHA-256
`4efcc949d3abf69f7050863139d465f21f2428b608f34be302f9c4f2937e4382`.
All baseline source hashes, TV438 artifact hashes, inherited clean-snapshot
artifacts, compiler identity, package paths, and candidate hashes were checked
before/after the current run. Shared dependency-file metadata was unchanged.
The original clean418 manifest did not record OLean or package byte hashes;
its inherited artifacts are bound by the TV438 reuse receipts and the current
snapshots, rather than an immutable artifact hash in the original clean run.

An earlier canonical attempt failed because a local instance attribute followed
a declaration docstring. That syntax placement was corrected and the complete
affected check rerun. No mathematical statement was changed. Failed logs are
retained locally. Focused preview evidence alone was not used as integration.

Compiler: `Lean (version 4.27.0-rc1, arm64-apple-darwin24.6.0, commit 2fcce7258eeb6e324366bc25f9058293b04b7547, Release)`.
Current manifest SHA-256: `10a64197a318d88cb077e8fcc85d10f05f6c041d881eefacbcc50d37262078a0`.
Source TeX SHA-256: `95ce19a9bcdb275c9d4c04e4b20e836c8e5f0965426e955999817e82141196d9`.

| Released Lean source | SHA-256 |
| --- | --- |
| `Formalization/RobustRL/ChiSquaredDensity.lean` | `9d691a02d3f1a063bd8f7f2d4b019d464e1b646da81dc2e84027895885289886` |
| `Formalization/RobustRL/ChiSquaredClippedMoments.lean` | `0350a8ac31de15202c320cd26cc23eb62f2c12c0c0deef3a016fe78d04f5b57b` |
| `Formalization/RobustRL/ChiSquaredLargeRadiusWitness.lean` | `78e10215d61a071fe4c080b4f9fd7c677c6bdc26be001e33548369350bb772c6` |
| `Formalization/RobustRL/ChiSquaredThresholdCrossing.lean` | `bc43f7b2961635b5b789523c84a45afb1f6b7f02d3aedcaa39730002988007a7` |
| `Formalization/RobustRL/ChiSquaredPositiveRootWitness.lean` | `11e9c4824f324bdbd36f40fbec6527fb0f119caab25deeb94df3ae062a0296d5` |
| `Formalization/RobustRL/ChiSquaredSmallRadiusWitness.lean` | `5b433af887923c290e7316995ac26fdb27c66a63bec11fab2a93faa6a936e2db` |
| `Formalization/RobustRL/ChiSquaredSupportedLevels.lean` | `f87d8a3c6439bfa9399178ed995c31bb0564645be619e77d6153e35fafe01c9c` |
| `Formalization/RobustRL/ChiSquaredZeroVarianceWitness.lean` | `4b6c6804a8c22b3c4636a29b0a2146016a48e832d48726f5e765388f2c312d3f` |
| `Formalization/RobustRL/ChiSquaredSourceMaximum.lean` | `9b8d09b0abfd17ea4f51fde9efa7b9f33601bd72bd5012594d07b283005a3148` |
| `Formalization/Statements/Ch7.lean` | `908f739cc1200f785bf16b86a676526e3078fb03f463835d3795aa5a07734622` |
| `Formalization/Statements/Ch7Proofs.lean` | `dc1cfe287edfa2156666885abf01aa0d0ac28251feda58363cee2302ee3ee474` |
| `Formalization.lean` | `f54751e8e64d45fc2816a425df35bc3b768fa163b130da22796bff4789af45c1` |

## Reproduction and accounting

From the repository root, `python3 scripts/check.py` compiles every project
module and audits the full namespace without rebuilding dependencies. That
performs a fresh full-project check, unlike the affected historical run above.
The repository's `bash scripts/lean-local.sh` wrapper can check focused modules
in import order; always include the full facade and axiom audit for integration.

The ledger counts the original two-branch Lemma 7.1 once. Its former TV-only
variant entry has been superseded. The ledger now has 17 reviewed named-result
entries, including their existing disclosed restrictions, plus one corrected
optimism variant. This is not a percentage of the entire monograph.
