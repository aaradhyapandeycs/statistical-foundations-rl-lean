# Independent review: Chapter 2 Lemma 2.3, v2 qualification

## Source and statement

Reviewed `lem:basic-property-matrix-notation-inf`, `source/upstream/tex/chapters/prelim.tex:544–574`, together with the randomized stationary-policy definition at `prelim.tex:66` and matrix-norm definition at `chapters/intro.tex:204–209`.

The v2 proposition at `Lemma2_3StatementV2Draft.lean` (SHA-256 `071aac8567a354cfc4e3a4a8fa3e56abcad83754d4dc2cb0cfa8a0bf8ac9dca2`) retains arbitrary finite state and action types and `StationaryPolicy`. Its state transition matrix is `Pπ(s,t)=Σa π(s)(a) P(t|s,a)`; its state-action matrix is `P^π((s,a),(t,b))=P(t|s,a)π(t)(b)`. These are the correct row-stochastic orientations. The statement covers every `0 ≤ γ < 1`, including `γ=0`, and for each matrix requires the genuine inverse's Neumann expansion, its action on the all-ones vector, the source's maximum row-wise absolute-sum norm, and entrywise nonnegativity. No invertibility premise is assumed.

The pure definition provider `PolicyMatrixDefinitionsV2Draft.lean` (SHA-256 `653936b4d467d495c358c24d6a6d61d9a283cf6f10849a9e595e79a262a7fdb7`) defines the two matrices directly from the model and policy. `PolicyMatrixResolventV2Draft.lean` (SHA-256 `03ad25a2196fd3e544dd60610a533333557beb25db79f1bdbc90437924b9f467`) proves both are stochastic and applies the general resolvent result. Its invertibility witness is constructed from the two-sided geometric-series identities; it is not a changed norm instance or a hypothesis. The wrapper `Lemma2_3ProofsV2Draft.lean` (SHA-256 `6e10b71c8010379f354550980beb56797396c0e04e07d5aeff28d2f8f10d19cf`) consumes that provider and discards only the additional invertibility output.

## Transformation and terminal evidence

The v2 mapping SHA-256 is `45a816482a6ba3c2fd83c0a084acfd65c3b029621ecc5aa7f8b41fe7de67a899`; runner `6b59ece9cb4571fbf2ec677acfb47f9227330adf761adae78dcafffe6eb46114`; pins `36518378004ba1bce3fa034dc91f89760011f6fff019c37778d84dca241bee51`. The four provider transformations are import remaps only. Ch2's only additional context change is the reviewed scope correction from `open scoped BigOperators` to `open scoped BigOperators Matrix`, needed for the matrix-vector notation; the full generated Ch2 and Ch2Proofs files are checked against their pinned base-plus-addition transformations. V1 is excluded: its Ch2 candidate failed on that scope omission before any successful index qualification.

Terminal status `run-1/status.json` SHA-256 `c1b6be94804469e17005c925115468750697023584eedfa85e035da485165e13` records six provider/index targets and one probe, all exit 0. The 14 ordered exports in `run-1/06.log` (SHA-256 `f2242fba1c71295a1bbada41a53150d91dab70f30d5351a8a5adab2d8ce980bc`) depend only on `propext`, `Classical.choice`, and `Quot.sound`. Source, captured source, OLean and log hashes are recorded for all seven steps; package metadata was unchanged. The run stages the pinned 833-module baseline, replaces the two old Ch2 index OLeans, and compiles the four providers, both indexes and probe in an isolated library.

## Affected integration and scope

The affected integration completed successfully. Its manifest SHA-256 is
`1103deecaf13b7286570f1b4c080cbaf301bf4cf0b949654bedda988ccc9ea6c`; the
check log SHA-256 is
`45ee562b8cd8b453526184253bf87842c0579a3dcd622b75764559414ffc8557`.
The run rebuilt 8 modules and verified 829 reused modules, for 837 sources
total. The full-library axiom audit covered 7,616 declarations. This is an
affected rebuild with retained verified reuse, not a clean rebuild of all
837 modules.

The reviewed statement, provider, wrapper, source scope, and standard-axiom
results above are now supported by both focused qualification and the
affected integration. This certifies the indexed Lemma 2.3 result only; it
does not certify the rest of Chapter 2 or the monograph.
