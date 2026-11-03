# Independent source review: synchronous Q-learning iterate bounds

Reviewed `.local/QLearningIterateBounds.lean`, SHA-256 `594b96eede407a268bad69041146728a7456478c39c53990c53bef006a5b207e`, against `source/upstream/tex/chapters/generative_model_model_free.tex`, Lemma `lemma:non-negativity-Qt-Vt` (lines 1052–1068) and its proof (Appendix B, lines 2508–2530). The later compiler audit verified this same current hash; there were no source changes after the review.

## Verdict

PASS for the pathwise bounded-iterate lemma and its immediate sup-norm error consequence. The staged recursion is synchronous: update `t+1` uses the previous full Q array at every coordinate and selects its value at the current coordinate's sampled next state. This is exactly the source update `Q_t=(1−η_t)Q_{t−1}+η_t(r+γP_tV_{t−1})`; no sequential in-place update is introduced.

The proof assumes `Q₀(s,a)∈[0,H]` and only the rates actually used, `η_k∈[0,1]` for `1≤k≤t`. The printed source assumes this for all times (and also states the unused `η₀` bound), so the staged prefix form is no stronger. It covers `t=0` with no rate hypotheses, permits arbitrary sample arrays, and requires no independence or sampling-law premise because the conclusion is pathwise. The reward and discount conditions come from the `DiscountedMDP` structure; `effectiveHorizon` is the proved `H=1/(1−γ)`, and its recursion `1+γH=H` bounds the Bellman target.

The value estimate uses the actual maximum over the finite nonempty action set. The final norm theorem compares every Q coordinate to `M.trajectoryExpectedQ M.optimalGreedyPolicy`, using the actual optimality fixed-point bounds and the proved equality between that trajectory Q and the greedy optimality fixed point. Since both arrays lie in `[0,H]`, the pointwise absolute difference and hence the finite-array sup norm are at most `H`. The source chapter's immediate consequence is therefore represented with the correct actual trajectory-Q reference.

## Scope

This module does not establish the generative sampling law, fresh-time independence, causality/measurability, martingale identities, concentration, a learning-rate schedule, or the later sample-complexity theorem. The builder handoff's separation of those obligations is correct.

## Independent compiler and axiom audit

Compiled the exact staged source with:

```sh
bash scripts/lean-local.sh -o .local/q-learning-iterate-independent-audit/QLearningIterateBounds.olean .local/QLearningIterateBounds.lean
```

Compilation exited successfully without diagnostics. An isolated import probe checked all six public declarations (`qLearningValue`, `qLearningIterate`, and the four bound/error theorems). Every export used only `propext`, `Classical.choice`, and `Quot.sound`. The production integration/export audit remains a separate check.

Production integration: the production module is byte-for-byte identical to the independently reviewed staged source. The full project export compiled and audited 2,610 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
