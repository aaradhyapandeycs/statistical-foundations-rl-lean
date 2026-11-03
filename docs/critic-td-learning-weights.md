# Independent review: TD learning-rate weights

Reviewed `.local/TDLearningWeights.lean`, SHA-256 `45cebbdcb5ff62d586b28932803ae727ec2f1d31bb814346c7e5886e3c19a59f`, against `source/upstream/tex/chapters/generative_model_model_free.tex`, definition `def:eta-k-t` (lines 307–312) and the surrounding TD-step-size statement/proof (317–327, 2286–2320).

## Source and semantic review

The helper uses the source contraction `1−η_i(1−γ)` and the finite suffix product over `i∈[k+1,t]`. For `k=0`, its source weight is the product from 1 through t; at `(t,k)=(0,0)`, the source's first and last cases overlap, and the staged definition deliberately gives the initialization branch precedence, hence weight 1. For positive diagonal indices `k=t>0`, the suffix product is empty and the result is `η_t`. The zero extension for `k>t` is an explicit convenience beyond the source domain.

The basic claims use only finite-prefix assumptions: `0≤γ≤1` and `0≤η_i≤1` for `1≤i≤t`. These make every contraction factor lie in `[0,1]`, yielding nonnegativity, and for positive k the product upper bound by one gives `weight≤η_k`. The helper's exponential estimate assumes the actual per-index suffix lower bound `α≤η_i(1−γ)` and counts exactly `t−k` factors. Applying `1−x≤exp(−x)` gives the stated exponential upper bound, with the initial coefficient bounded by one. The proof does not assume any schedule theorem or smuggle a schedule-derived contraction premise into the conclusion.

## Exact-source compiler and axiom audit

Verified the staged SHA above, then compiled the exact file with:

```sh
bash scripts/lean-local.sh -o .local/td-weights-independent-audit/TDLearningWeights.olean .local/TDLearningWeights.lean
```

Compilation exited successfully without diagnostics. An isolated import probe checked all nine declarations: `tdRateContraction`, `tdRateWeight`, and the seven endpoint/bound lemmas (`tdRateWeight_initial`, `_diagonal`, `_out_of_range`, `tdRateContraction_bounds`, `tdRateWeight_nonneg`, `_le_rate`, `_le_exp`). Every export depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Scope and source caveat

This helper supplies the exact weights, endpoint conventions, interval bounds, and a generic finite-product exponential estimate. It does **not** prove the named source TD-step-size lemma. In particular, it does not establish the schedule-specific lower bound on `η_i(1−γ)`, discharge the additional gap-dependent large-T premise used in the source appendix, repair the lemma's missing `t≤T` condition, or prove any TD concentration/rate theorem. The separate source caveats and schedule argument in `docs/source-td-learning-weights-plan.md` remain applicable.

Production integration: the production module is byte-for-byte identical to the independently reviewed staged source. The full project export compiled and audited 2,610 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
