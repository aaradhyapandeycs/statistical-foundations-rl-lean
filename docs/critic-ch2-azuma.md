# Independent review: Azuma–Hoeffding source-facing result

## Source and exact candidate

The displayed source is `lem:azuma-hoeffding`, `source/upstream/tex/chapters/prelim.tex:1038–1052`. The source Prop was independently reviewed at `Ch2AzumaAddition.lean`, SHA-256 `b9b6031e0aec386d253927f5acdc17045fdf4c3fd560dcefa5d62128eeb4b732`; its standalone exact statement SHA-256 is `1cc74e1e9f3eed7d9fa77a8631f777c467113fc904c65f51d94ddfed0f4aead3`.

The final candidate files are `tree/Formalization/Statements/Ch2.lean`, SHA-256 `b32c0bebe4a35cd275ef1159da00d4821df52a2aac45e59b79b49c4cbcab15c3`, and `Ch2Proofs.lean`, SHA-256 `c249303630060f5285879733771bcef4dd187825838f956f58bdbcef09370bc8`. The Ch2 addition matches the reviewed Prop; its proof wrapper applies the compiled `azuma_natural_history_source` export directly. No extra proof assumption is introduced.

## Transformation and build evidence

The seven canonical helper modules preserve the reviewed declaration bodies while changing their module/import surfaces. Their source and artifact pairs are pinned in the mapping and verified against the original successful helper receipts. The two index modules are based on the pinned 826-module source snapshot; only the intended Ch2 Prop and applying proof addition are present. The guarded run-1 status is SHA-256 `ac1f0affaf598eff0df3f391bb274d1577e31d9a9f36a036e177173aeb5a7479`; all nine targets and the 12-export probe exited 0. Probe log SHA-256 `b07c64666f3583b9c9beaf754177cb1bca6e08363e76557d2eab33711e8e92ce`; all exports report only `propext`, `Classical.choice`, and `Quot.sound`. Mapping SHA-256 `41f380b353b952a8bd283460f276a6a80f88ebd80724e36ef91f5113aca7b5e0`; runner SHA-256 `3b60d7b67c8c9a20437c6c4ebd2a7f77959884efb7c602e63301ec56aed35309`; pins SHA-256 `aa7c85dca0a7fe029b7751cc8c594938022f027443bacdf72740a5940defa211`.

## Review conclusion and limits

The Prop preserves the arbitrary probability space, measurable real increments, deterministic pointwise varying bounds, a.e. conditional centering on precisely the preceding increments, all natural `n` including zero, the strict probability endpoint `1−δ < μ(event)`, and the exact radius. The compiled natural-history result derives bound nonnegativity and integrability from the source premises, handles zero total proxy directly, and uses the strict two-sided tail for the positive-proxy case. The index wrapper consumes that result without strengthening the Prop.

This establishes the reviewed Lemma 2.8 candidate and its focused 826-baseline affected build only. It is not a whole-Chapter-2 or whole-project clean-build claim, and it does not certify other paper statements.

## Affected integration evidence

I independently checked the terminal affected integration manifest at run
`20261105T005559058914Z`, SHA-256
`3945e14acc01e80fc102db7d41851e9dee79444b0ff67f36d54a84bf376d8422`.
It records all 833 project sources, 11 rebuilt modules and 822 verified reused
modules, with the full standard-axiom audit passing for 7,597 declarations.
Every candidate source and every OLean hash in the manifest rehashed
successfully. The terminal check log SHA-256 is
`10c6fa356eab03ef5dbdfc2dd3804d5b481ee7a81021e2f182c878dbf6439945`.
This is an affected rebuild with verified reuse from the 826-module baseline,
not a fresh clean 833-module build.

The generated verification record also preserves the 9-target/12-export
focused qualification result, and the generated coverage row and progress
entry identify only Lemma 2.8. The ledger is 21 original results and 10
corrected variants. This evidence does not claim the rest of Chapter 2 or the
whole project is complete.
