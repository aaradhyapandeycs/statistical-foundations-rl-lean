# Deterministic empirical-value variance/resolvent bridge

Source: `source/upstream/tex/chapters/generative_model_model_based.tex:1379–1415, 2637–2715`, `eq:empirical-value-residual-bound`, `eq:empirical-value-variance-bound`, and `lem:empirical-value-residual`; source SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

`.local/PolicyLearningVarianceResolventBridge.lean` composes the independently reviewed empirical-value variance self-bound with the staged true-resolvent order/Jensen bridge. For valid M,H with the **same** reward and discount, an arbitrary stationary policy π, `h=1−γ>0`, `W=H.trajectoryExpectedValue π`, `z=P̂π W−Pπ W`, `σ=Var_{Pπ}(W)` and the actual true inverse `R=(I−γPπ)⁻¹`, it proves

```text
γ² ‖Rσ‖∞ ≤ 2/h² + (2γ²/h) ‖R|z|‖∞,
γ² ‖R√σ‖∞² ≤ 2/h³ + (2γ/h²) · (γ ‖R|z|‖∞).
```

These are unconditional deterministic consequences of actual Bellman/value bounds; no sign assumption on the true-kernel forcing `r+γz` is imposed. The proof transports the actual pointwise variance inequality through the positive true inverse, cancels the actual inverse against `I−γPπ`, drops the nonpositive `−W²`, and applies generic inverse Jensen. The second inequality retains the stronger factor γ multiplying `S=γ‖R|z|‖∞`; the source subsequently weakens using `γ≤1`. All statements cover γ=0 without dividing by it.

Given only nonnegative `a,b` and the **explicit intermediate row premise** `|z(s)|≤a√σ(s)+b` for every state, a further deterministic theorem derives the self-bounding relation. With `N>0`, `β≥0`, `a=√(β/N)`, `b=2β/(Nh)`, it proves the source's exact constants

```text
γ ‖R|z|‖∞ ≤ 2√(2β/(Nh³)) + 6β/(Nh²).
```

It uses the reviewed scalar AM–GM closure; the desired norm inequality is **not** an assumption. The file separately proves the exact true-inverse value difference identity `W−Vπ = γ Rz`, derives `‖W−Vπ‖∞≤γ‖R|z|‖∞`, and concludes the same source radius for actual value-evaluation error under the explicit row premise. `policyEstimator_source_error_bound_conditional` specializes this deterministic result to the actual sample-built empirical model and that same data-dependent greedy policy; `hr` and `hγ` are discharged definitionally. It does not assume the fitted policy is sample-independent.

These are conditional deterministic results, not yet an actual-law event or a claim of the entire named source lemma. A later step must derive the fitted-policy row premise from the already established all-action empirical-optimal residual event, identify the selected deterministic policy's true and empirical policy rows, and transport the same event by inclusion. Combining with the fixed true-optimal policy's evaluation error, final log/sample arithmetic, source assumptions and integration is also separate. No statistical independence for the fitted policy or nonnegative empirical forcing may be introduced during assembly.

Validation: unchanged staged `PolicyLearningTrueResolventJensen.lean` and `PolicyLearningEmpiricalVarianceSelfBound.lean` were rebuilt to project-owned `.local` oleans, then `lake env bash -c 'export LEAN_PATH="$PWD/.local:$LEAN_PATH"; lean .local/PolicyLearningVarianceResolventBridge.lean'` passed without diagnostics. An exact-source temporary probe checked the inverse variance bound, Jensen consequence, self-bounding relation, source residual bound, exact true-inverse identity, generic value-error bound and actual fitted-policy specialization; all seven reported only `propext`, `Classical.choice`, and `Quot.sound`. Staged file SHA-256 `ddc7b3c954362ffad70c249d9ac37c2aa5b726be402a0d733f5471bbb800741b`; staged Jensen dependency `0adf2b1d01b4c4463f5c6fec291e1fe549afc76be242374a2d744f72b2d00a2e`; staged self-bound dependency `55c8045d77c988c70228066f28f485e134de5ca1a78ebf8ce6a760bd7e24c95c`. Independent source/semantic review and production-export validation remain outstanding.
