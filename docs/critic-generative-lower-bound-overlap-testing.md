# Independent review: finite overlap and binary testing

**Verdict: pass for the stated actual-finite-law overlap/testing and scalar strictness lemmas.** The KL-to-overlap/Pinsker bridge and minimax lower bound remain open.

The source binary-testing step `generative_model_model_based.tex:1694–1722` needs a lower bound on testing error for the two actual data laws, then uses the strict 0.1 threshold. Here `finiteOverlap μ₀ μ₁` is literally `Σ_x min(μ₀.real{x}, μ₁.real{x})` on a finite type with probability measures. It is not a symbolic label for KL, a placeholder hypothesis, or an assumed testing lower bound.

For an arbitrary Bool-valued test, the theorem uses `true` as choosing model 1. Hence `μ₀{test=true}` and `μ₁{test=false}` are correctly oriented error probabilities. On each finite atom, the overlap minimum is bounded by whichever of these two errors is charged there; summing gives `overlap≤error₀+error₁`, and elementary max arithmetic gives `overlap/2≤max(error₀,error₁)`. Measurable singleton hypotheses on a finite type make all test sets measurable; no separate independence or pointwise test-measurability assumption is missing in that finite discrete setting. The statement covers arbitrary deterministic data tests, including constant tests and zero-overlap/identical-law endpoints. Randomized tests require their own seed/mixing formalization.

`sourcePinskerBranch_strict` is a **scalar numerical lemma**: if β≤9/10 then `(1−√(β/2))/2>1/10`. Its proof includes β=9/10 and uses `√(9/20)<4/5`, since `9/20<16/25`. It does not assert β≥0; Lean's real square root is zero on negative arguments, so the mathematical inequality still holds, while an eventual KL application must supply the usual nonnegative β. The strict conclusion is enough to repair the source proof's otherwise omitted step from a merely `≥0.1` test bound to the printed strict `>0.1` estimation failure, as documented in `source-generative-lower-bound-testing-bottleneck.md`.

Nothing in this module relates `finiteOverlap` to actual KL, proves Pinsker/Fano, identifies the hard-MDP data laws, handles arbitrary estimators, or proves a lower-bound probability. In particular, the numerical square-root lemma is not itself a testing theorem. A later proof must establish the KL-to-overlap estimate and connect the actual finite experiment before composing the results.

Staged source SHA-256 `6f903b9aa711401403fe9d4c13a9c62b8b51ce335678426ab043f4b1f56a3dbb`; source chapter SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. An exact unchanged source copy with original imports and four appended axiom checks compiled independently, exit 0. The definition and all three theorems use only `propext`, `Classical.choice`, and `Quot.sound`; the two `simpa` linter warnings match the builder's report and do not affect the result. Production export verification remains separate.

A repeat independent exact-source check alongside TestingReduction also compiled, with the same two nonsemantic `simpa` warnings and the same standard-only axiom result for all four declarations.

## Integrated production audit

Production `Formalization/Generative/GenerativeLowerBoundOverlapTesting.lean` is byte-identical to reviewed SHA `6f903b9aa711401403fe9d4c13a9c62b8b51ce335678426ab043f4b1f56a3dbb`. It compiled with the same two `simpa` linter warnings as staged; all four imported exports use only `propext`, `Classical.choice`, and `Quot.sound`. The initial attempt to use a sparse isolated `LEAN_PATH` failed because it shadowed the existing production dependency tree; recompiling these requested production modules into the project build directory and then auditing actual imports succeeded.
