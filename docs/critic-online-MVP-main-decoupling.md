# Independent review: corrected MVP decoupling and main regret

## Source claims and exported statements

The decoupling source is Lemma 5.14, `lemma:decouple`, at `source/upstream/tex/chapters/onlineRL.tex:1722–1744`. The main regret source is `thm-mvp-regret` at `:1339–1352`. The main result is identified here by its source label `thm-mvp-regret` and exact source lines.

The indexed statements and applying wrappers are [`Lemma5_14_corrected`](../Formalization/Statements/Ch5.lean), [`Lemma5_14_corrected_holds`](../Formalization/Statements/Ch5Proofs.lean), [`MVP_regret_corrected`](../Formalization/Statements/Ch5.lean), and [`MVP_regret_corrected_holds`](../Formalization/Statements/Ch5Proofs.lean).

## Corrected Lemma 5.14

The proposition states all three source decoupling bounds on one event under the actual reset-and-transition trajectory law: `T₁ ≤ W₄`, `W₄ ≤ √(SAH·I·T₆) + SAH²I`, and `W₃ ≤ √(SAH³·I·T₆) + SAH³I`. It uses the learner's retained empirical rows, completed pre-episode history, capped backward values, and fixed maximizing tie rule. Its assumptions are positive `H,K`, `0 < δ ≤ 1`, `c₁ ≥ 4`, `c₂ ≥ c₁²`, and the displayed eligibility condition `SAH log₂ K ≤ K`. It keeps the source allocation in corrected reciprocal form `δ′ = δ/(100 S²A²H²K²)` and the stated information factor. The success probability is strict, `> 1 − δ′`. The `K=1` endpoint is proved directly with zero information factor and the actual `H` transition outcomes.

The applying proof discharges the row-carrier, sample-history, profile, concentration, and sequential-law bridges in the proof, rather than putting a confidence or semantic certificate in the source proposition. The focused Ch5/Ch5Proofs build compiled both index files and checked 20 actual exports. Its receipt SHA-256 is `d4c94c84e810166c598dabe8c255a45e1a3545b8eebe527fc65303fa153f3b54`; the probe log SHA-256 is `4375dd7e6839065a17cc664ccd0cf73c9c653b8ae347e31facf3749607c526cb`. The export audit permitted only `propext`, `Classical.choice`, and `Quot.sound`.

## Corrected main regret result

The main proposition gives one universal witness `C = 100`, quantified before the environment parameters. For every finite nonempty state/action model, positive `H,K`, and `0 < δ < 1`, it bounds actual regret by

\[
100\max(1,I)\min\{\sqrt{SAH^3K},HK\}
\]

with probability at least `1 − δ`, where `δ′ = δ/(100 S²A²H²K²)` and `I = 40000 (log₂ K)³ log(3SAH) log(1/δ′)`. The policy whose true trajectory value appears in regret is the same committed-history planner used under the actual sequential law; the comparator is the true-environment greedy optimal policy. The result includes `K=1`, where the direct branch handles the zero information factor. The large branch establishes the decoupling confidence and eligibility conditions internally. No hdecProb premise remains.

The focused corrected-decoupling tail compiled two providers and its actual export probe. The tail status SHA-256 is `06a7fd3517a1da6d2f61579c826dd921d30b6f1615076d93f80ee3309d0de20c`; its probe log SHA-256 is `8aeb8f20b95ddab2e5537342b6ebf3b594260d3654f642ff28e8c7b0d1c49ddd`. The main source run compiled four target modules and checked six actual exports; its status SHA-256 is `67aee2634e4cf1865054a06e8f270d1d18e0e320031ec65283ed8211004a24bf` and probe log SHA-256 is `4e2cfbe1c1ab2f53272b549187ef506c292f193d3eebd348f0cc51aff05c8b9c`. Both probes reported only the standard axioms. The exact focused source/index versions are included in the frozen 913-module assembly.

## Corrections and limits

The corrected result visibly records finite zero-count completion and analysis charge (C8), K=1 handling (C12), the power-of-two trigger interpretation (C13), the safe ceiling profile cover (C15), reciprocal confidence allocation (C16), and the terminal-zero continuation family (C17), together with one fixed maximizing tie. The downstream actual-MVP construction uses the documented power-of-two trigger correction (C13); the generic concentration theorem does not certify the literal pseudocode. These corrections are not author approval and do not verify the printed algorithm where its literal code or proof differs.

The fresh project integration check completed successfully on the frozen 913-module assembly: all 913 modules were rebuilt with zero project-artifact reuse, and the final audit passed for 8,162 declarations. Guarded manifest SHA-256: `750510fd73526d1592be0e61dd64f468fc1b286f50012c44037a3a15ae05de81`; run `20261105T030921935125Z`; check log SHA-256 `47235ef53612bb2f89d69f48b8edfdfba5ec83cb3dd5899b4dfdf6b372c1f2e0`. The audit reports only the standard axioms, and the frozen source/OLean, focused evidence, and configuration pins were reverified. Shared dependency metadata was stable by path, size, and modification time; no byte-seal claim is made for those caches. This report does not claim that the entire monograph is complete.
