# Independent review: TD main-budget discharge of the large-T premise

Reviewed `.local/TDStepSizeBudget.lean`, SHA-256 `dbb67852b00236a92327299c7baee6fbbf83698d2f20bc8d9ec05d1dd413e7cc`, against source Theorem `thm:policy-evaluation-TD` and sample budget in `source/upstream/tex/chapters/generative_model_model_free.tex:204–224`, together with the corrected early/late helpers. The literal source budget used is
`c₃ log(T)^3 log(ST/δ) / ((1−γ)^3 ε²) ≤ T`.

## Source/semantic review

PASS for the scalar implication and the stated corrected weight wrapper. Hypotheses explicitly preserve `T≥2`, `S≥1`, `0<δ<1`, `0<ε≤1/(1−γ)`, `γ<1`, positive `c₁,c₃`, and the budget. The final wrapper additionally has the source range `0≤γ`, positive `c₂`, `c₁c₂≤1/8`, the finite schedule, `t≤T`, and the source time threshold. Thus all denominators and logarithm domains needed by the proof are positive.

Since `ST/δ≥T`, `log(ST/δ)≥logT>0`. Since `ε(1−γ)≤1`, we have `ε²(1−γ)²≤1`. Clearing the positive budget denominator and combining these inequalities gives `c₃log(T)^4≤T(1−γ)`. The explicit universal-constant relation `1≤c₁c₃(log2)^2`, together with `logT≥log2>0`, yields `log(T)^2≤c₁c₃log(T)^4`. Multiplying the normalized budget inequality by positive `c₁` then proves the exact additional source-proof premise `log(T)^2≤c₁(1−γ)T`.

`exists_td_budget_constant` supplies `c₃=1/[c₁(log2)^2]` for any fixed universal `c₁>0`, so the relation is satisfiable independently of S,T,γ,δ,ε and the schedule. The wrapper invokes the corrected combined early/late theorem with the derived large-T fact, rather than assuming it. The helper requires only `γ<1` for the scalar discharge; the final wrapper imposes `γ≥0`, and the source theorem's `γ≥1/2` is therefore covered.

## Exact-source compile and axiom audit

Verified all four staged hashes and ran `.local/audit-td-step-size-budget-independent.sh`, which rebuilt `TDLearningWeights`, `TDStepSizeEarly`, `TDStepSizeLate`, and `TDStepSizeBudget` in dependency order under `.local/td-step-size-budget-independent-audit`. Compilation and import probing exited successfully without diagnostics. `#print axioms` covered 18 declarations; all use only `propext`, `Classical.choice`, and `Quot.sound`.

## Limits

This proves only that the printed main sample-budget inequality discharges the added early-weight premise under the explicit constant relation. The relation is a sufficient lower bound on `c₃`; it does not certify that a chosen constant satisfies every other “sufficiently large” requirement in the source theorem's stochastic proof. The late branch and corrected combined helper are proved separately. No TD concentration or accuracy theorem is established by this scalar budget lemma, and production integration remains separate.

Production integration: the reviewed source body compiles in the project export with qualified imports; the Q-learning causality file has been given the production module name `QLearningCausality`. The full project check audited 2,755 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
