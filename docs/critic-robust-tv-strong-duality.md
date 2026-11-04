# Independent source audit: robust-RL TV duality branch

**Scope:** source and statement audit of the canonical TV-only Chapter 7
candidate. The affected integration check was still running at the time of
this review; this note does not report it as passed. The χ² branch and full
named Lemma 7.1 are not covered or counted as complete.

## Source statement

The source is `source/upstream/tex/chapters/robust_RL.tex`, Lemma
`lemma:dual-form`, lines 302–324. The surrounding setup at lines 31–32 sets
the uncertainty radius to `σ > 0`. In the TV case, the lemma states the
infimum of the expected value over the TV uncertainty set equals the maximum
over `α ∈ [Vmin,Vmax]` of

`⟨p, [V]α⟩ − σ (α − min_s [V]α(s))`.

The lemma assumes a finite nominal probability vector and `V ≥ 0`. This audit
covers only the TV bullet at lines 307–312. The separate χ² bullet at lines
314–321 remains open. See [the source-issues ledger](SOURCE-ISSUES.md) for the
project’s branch-scope accounting.

## Statement and proof correspondence

The expanded proposition `StatisticalRL.Statements.Ch7.Lemma7_1_tv` has the
full finite-carrier quantification, an actual `FiniteDistribution`, pointwise
nonnegative `V`, and `σ > 0`. Its primal is an infimum over the subtype of
actual finite distributions satisfying the source half-L1 TV constraint. Its
dual uses the clipped finite expectation, the minimum of the clipped vector,
and the same source radius. It gives an α in the full interval from the finite
minimum to the finite maximum, states equality with the primal infimum, and
states dominance over every β in that interval. The last clause makes the
witness a literal maximum; existence of an equal-valued point alone would not
be sufficient.

The proof wrapper consumes the existing event-TV/half-L1 identity to rewrite
the actual feasible-row predicate, identifies the explicit subtype infimum
with the reusable primal infimum, and applies the source-maximum result for
both equality and the all-β comparison. The normalization is half-L1, so the
radius is in total-variation units, with no extra factor of two. There is no
`DecidableEq` premise in the printed proposition. The statement is
universe-polymorphic, requires only a finite nonempty state carrier, and adds
no `σ ≤ 1` restriction. Zero nominal atoms, tied values, singleton carriers,
and radii above one remain in scope.

The statement file directly imports the definitions-only
`Formalization.RobustRL.TVWeakDefinitions`; that module contains no theorem
commands. Its foundational imports include theorem-bearing modules, consistent
with the project’s direct-import definition-only convention. The proof file
imports the theorem modules separately.

## Canonical candidate and exact source binding

The canonical candidate is the versioned 438-module affected-rebuild snapshot
used by integration session 50797. Its source identity is recorded in the
integration state and the hashes below. In the current workspace, the
corresponding production-layout files are not yet landed; use these paths and
hashes to identify the audited candidate before promotion.

| Candidate module | SHA-256 |
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

The 17 renamed proof modules were checked against their frozen source map.
All executable source suffixes match their focused preview byte-for-byte;
only the module documentation changed in `TVTransfer` and `TVStrongDuality`.
The Ch7 statement and wrapper are byte-identical to the successfully
compiled expanded v2 sources. The documentation-only edits do not change
declarations or proofs.

## Build and axiom evidence

The focused preview evidence is limited to the exact expanded Ch7 sources.
The statement and wrapper each compiled with exit 0 in run-v2; the active
probe also exited 0 and reports `propext`, `Classical.choice`, and `Quot.sound`
for the source-maximum and Ch7 wrapper exports. These focused receipts establish
neither the current 438-module affected integration nor a new clean rebuild.
At review time, integration session 50797 was still running after only two
completed logs. No result is claimed for that run here.

This audit supports promotion of the TV-branch candidate only after the
affected integration check succeeds and its source/artifact manifest is
reviewed. It does not certify the χ² formula or the complete source Lemma 7.1.
