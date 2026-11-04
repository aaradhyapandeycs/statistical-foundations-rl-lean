# Robust-RL total-variation duality branch: verification record

This is the historical TV-only milestone record. Both branches are now
verified; see the [full Lemma 7.1 record](robust-strong-duality-verification.md).

**Status:** the total-variation branch of source Lemma 7.1 is formalized and
verified. The chi-squared branch remains open; the full two-branch named Lemma
7.1 is not counted as complete. The monograph remains incomplete.

## Source statement and reviewed scope

The source is `source/upstream/tex/chapters/robust_RL.tex`, label
`lemma:dual-form`, lines 302–324 (TV bullet 307–312). The surrounding setup at
lines 31–32 gives `σ > 0`. For any finite nominal probability vector `p` and
nonnegative value vector `V`, the TV bullet equates the infimum over the source
TV uncertainty set with the maximum over `α ∈ [Vmin,Vmax]` of

`⟨p,[V]α⟩ − σ (α − min_s [V]α(s))`.

The source macro `\ror` expands to `σ`; the Lean TV radius is in the source
half-L1 total-variation units. There is no additional factor of two. The
formalized statement includes the actual finite-row feasible subtype, the
primal infimum, an interval witness, equality, and dominance over every scalar
in the interval. It is universe-polymorphic and has no `DecidableEq` premise.
It covers zero-mass nominal atoms, tied values, singleton state carriers, and
all `σ > 0`, including radii above one. It does not certify the χ² bullet at
lines 314–321 or the full named lemma.

The proof chain identifies finite event-TV with half-L1, proves the clipped
objective comparison, constructs a feasible statewise removal allocation by
finite sorted cost levels and tie filling, matches the resulting payoff to the
clipped objective, and combines the two inequalities. Compactness and
continuity supply an interval maximizer; the exported result also states its
maximality against every interval point. The wrapper consumes that result for
both the primal equality and the full `∀ β` maximum clause.

The statement index is `StatisticalRL.Statements.Ch7.Lemma7_1_tv`; its proof is
`StatisticalRL.Statements.Ch7.Lemma7_1_tv_holds`. The source maximum export is
`StatisticalRL.RobustRL.TVProof.SourceMaximum.tvPrimalInf_eq_source_max`.
The TV definitions were extracted into `TVWeakDefinitions`, a definitions-only
direct import for the statement module. In `TVWeakDuality`, the existing
theorem bodies are unchanged; the definitions were moved and the module imports
the new definitions module. No other pre-existing theorem statement or proof
was changed for this result.

## Source identity

The authoritative TeX source hash is
`95ce19a9bcdb275c9d4c04e4b20e836c8e5f0965426e955999817e82141196d9`.
The canonical integration manifest SHA-256 is
`003ee94561cb5b2ee202a53e915498df09421e940f37fcdc1badef10499fdfb3` for run
`20261104T042408678366Z`. The integration state reports that all 438 Lean source
hashes matched the candidate snapshot; the 22 files below comprise the 21-file TV overlay and the updated root facade.
Their source hashes match the current working files.

| Released Lean source | SHA-256 |
| --- | --- |
| `Formalization/RobustRL/TVEventBridge.lean` | `7e9e3c3cd98e0a83576a1a3da5073fa9dae8041b409bd49ac8b27b8978a2c2c2` |
| `Formalization/RobustRL/TVClip.lean` | `2295e64900b73a86b159ac472a4bea9cf044195bf4ba7b4f21ddb9764e087eb0` |
| `Formalization/RobustRL/TVClipThresholdIdentity.lean` | `6eb78c1b66e24117e1e5c6e2b9bcfc510094d0597d8d31faa5cc1c993f55a9c2` |
| `Formalization/RobustRL/TVTransfer.lean` | `96de9841852b1c14de2a54daf36d7550f908547c3d54b804bc404c385c3c0029` |
| `Formalization/RobustRL/TVCostLevels.lean` | `a77c4cf6aa7614ffd501e66749ecc1b698dc816c9063033e0e489f4c6bc9ce74` |
| `Formalization/RobustRL/TVDisaggregation.lean` | `e7398e2c7cd6727299cd19c2aad003e3ffd436b89825e0f1203ed16596f88fb4` |
| `Formalization/RobustRL/TVPrefixCrossing.lean` | `67cf07479b5454d0bc33e2d869022c4df1c4dbae53f1e6478276c1d85ce6cf5f` |
| `Formalization/RobustRL/TVSortedCrossing.lean` | `9225c9ffab5b38a564046e9bae22f82e906c77ec72260b9057668efa886b4a34` |
| `Formalization/RobustRL/TVTieFill.lean` | `7e606d805faede36bd3bd4e71bc6733b5c52d827dce8dcf520635262b3c6ea78` |
| `Formalization/RobustRL/TVSortedStateMass.lean` | `d2f559a703bb1211d81852e3a1d6f2d0e5497b6314672bde4b277fa810fad7ae` |
| `Formalization/RobustRL/TVCrossingComposition.lean` | `74322f12a2642c54edc65b071e1910a93ebd74ea4cca91c262670598c44c208b` |
| `Formalization/RobustRL/TVSortedThreshold.lean` | `6322d4f4b88e511117ed75e0a103afae0fe9ec92c926303b026289e48174e96f` |
| `Formalization/RobustRL/TVPayoffCertificate.lean` | `611981de9201a49492b15fd4e3e2e0de986857ffc5df4fbbdeb2f0c7c71f16ad` |
| `Formalization/RobustRL/TVAllRadiusWitness.lean` | `1272dde4bd54577e3bd4178bd38d0be5088770c6ecebd42ccb659234ae8b65b9` |
| `Formalization/RobustRL/TVReverseInequality.lean` | `d0a3a1aaf526f869086be490e9dbea3bb3407a9db04f59493dda2c29ea77b0ca` |
| `Formalization/RobustRL/TVStrongDuality.lean` | `f7618fe301d682d081d097deccf649518ea458c1618fec3f68821f3c97107512` |
| `Formalization/RobustRL/TVSourceMaximum.lean` | `cc7044e50af134985d3daac50cc9c0f39019461dc742afcdfd6cd3aa827ba660` |
| `Formalization/RobustRL/TVWeakDefinitions.lean` | `9902f4d3c5d60299b4c8b28b12f2e8dbfc1c724031848449b5a97aa157b875c9` |
| `Formalization/RobustRL/TVWeakDuality.lean` | `2ba626cc042397806f743acde60964add3e90ddceaaed8420c4840a6510f188a` |
| `Formalization/Statements/Ch7.lean` | `39660bca24e41c43eb34c0935ea44644c5337e255ceb297e2478824466d0394c` |
| `Formalization/Statements/Ch7Proofs.lean` | `23995e225fbca2174753a52a612ddb4b7ac531732e1401184f825067f76211ae` |
| `Formalization.lean` | `d0f8947fed50c08e76a8152e4e4bc4b595698b3fe7cde695bad01b0b35235b53` |

## Build and axiom evidence

The focused candidate build compiled the expanded Chapter 7 statement and
proof wrapper, and the active actual-export probe passed. The source and proof
review is recorded in [the independent TV audit](critic-robust-tv-strong-duality.md).

The canonical integration run used Lean
`Lean (version 4.27.0-rc1, arm64-apple-darwin24.6.0, commit
2fcce7258eeb6e324366bc25f9058293b04b7547, Release)`. It completed with exit 0:
23 modules were rebuilt and 415 modules were reused from the previously
verified clean 418-module baseline, for the current 438-module source tree.
`Audit.lean` audited 4,959 project declarations and allowed only
`propext`, `Classical.choice`, and `Quot.sound`. This was an affected rebuild
against that verified clean baseline, **not** a fresh 438-module clean build.
The preceding baseline was Theorem 4.1's clean check (manifest SHA-256
`4efcc949d3abf69f7050863139d465f21f2428b608f34be302f9c4f2937e4382`).

The historical baseline did not contain byte hashes for external package
files. The affected-run driver checked that the compiler/package paths matched
the baseline and checked package-file metadata before and after the run; it
relied on the pinned, read-only dependency paths. The report records an incremental build against the documented baseline.

## Reproduction

From the repository root, `python3 scripts/check.py` performs a fresh project
build and transitive axiom audit of the complete current source tree without
rebuilding dependencies. This reproduces a clean full check, not the historical
affected-rebuild mode above. For a narrow source edit, use the repository's
`bash scripts/lean-local.sh` wrapper to compile affected Lean modules in import
order, then compile `Audit.lean`; do not substitute a helper-only or preview
build for the complete facade and project audit.

See [coverage status](COVERAGE.md) and [branch-scope disclosures](SOURCE-ISSUES.md).
