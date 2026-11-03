# Generic true-policy resolvent Jensen bridge

Source: `source/upstream/tex/chapters/generative_model_model_based.tex:295–326, 1379–1397`, especially `eq:Jensen-I-gamma-P-Var` and `eq:empirical-value-residual-bound`; source SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

`.local/PolicyLearningTrueResolventJensen.lean` proves deterministic order, normalization, Jensen and norm properties for the **actual literal** true-policy matrix inverse `R=(I−γPπ)⁻¹`, every stationary randomized policy π and arbitrary nonnegative input `z : State→ℝ`. No probability event, empirical variance self-bound or desired policy-learning error bound is assumed. All results allow the full `0≤γ<1` domain, including zero discount.

The proof derives nonnegative inverse images via a finite minimum principle for the genuine stochastic policy rows; applies this to coordinate vectors to derive nonnegative matrix entries; and proves `R1=(1−γ)⁻¹1`. It constructs the genuine `FiniteDistribution` row `d_s(t)=(1−γ)R(s,t)`, with nonnegativity and mass one proved from these facts. Its expectation is exactly `(1−γ)(Rf)(s)`. Jensen's finite-row square inequality then proves

```text
[(1−γ) R√z(s)]² ≤ (1−γ) Rz(s),
‖R√z‖∞ ≤ √(‖Rz‖∞/(1−γ)).
```

A further **conditional deterministic helper** consumes only explicit pointwise inputs `z≥0`, `a,b≥0`, and `|f(s)|≤a√z(s)+b` for every state. It proves

```text
γ ‖R|f|‖∞ ≤ γa √(‖Rz‖∞/(1−γ)) + γb/(1−γ).
```

Its row premise is an intermediate residual inequality and is actually used via inverse monotonicity; it is not a hypothesis of a claimed policy-learning theorem. The unconditional inverse/Jensen results can be applied to any realized fitted policy pointwise without claiming that policy is independent of the samples. To reach the source bound one must still identify the true-policy residual for that same fitted policy, obtain the rowwise event from the reviewed all-action event, and combine this bridge with the separately proved fitted-policy empirical-variance self-bound and numerical self-bounding solution. No final residual, value-learning, or sample-complexity theorem is asserted here.

Validation: `bash scripts/lean-local.sh .local/PolicyLearningTrueResolventJensen.lean` passed without diagnostics. An exact-source temporary probe checked inverse-entry nonnegativity, the normalized probability row, Jensen, the norm bridge, and the conditional residual bridge; all reported only `propext`, `Classical.choice`, and `Quot.sound`. Staged source SHA-256 `0adf2b1d01b4c4463f5c6fec291e1fe549afc76be242374a2d744f72b2d00a2e`; integrated `PolicyEvaluationVarianceResolvent.lean` dependency SHA-256 `d971ae8c37d878fc3a64ed10f0c87ec4a9883abc6c2c210d6492b9e7bbe734de`. Independent source/semantic review and production export validation remain outstanding.
