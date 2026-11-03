# Empirical versus true policy-resolvent comparison

`.local/PolicyEvaluationEmpiricalResolvent.lean` proves the exact empirical/true finite-matrix resolvent identity, an unconditional deterministic norm comparison, and an actual-sampling-law Bernstein comparison for the fixed true-policy variance vector. It also bounds the empirical square-root-variance resolvent by the already reviewed true-resolvent bound plus an explicit **higher-order** Bernstein radius. This is a staged intermediate toward the source's sharp policy-evaluation theorem, not a proof of the horizon-three sample complexity. Independent review and integration remain pending.

## Source and notation

The source identifies the key empirical-versus-true comparison in `generative_model_model_based.tex:379–405`, label `eq:key-quantity-sharp-analysis-MB-PE`, then defines recursively the true auxiliary value `V^(1)=(I−γP_π)⁻¹ sqrt(Var_{P_π}(V^π))` at lines 414–433 and applies Bernstein to higher auxiliary values at lines 461–480. Its sharp proof continues with a multilevel recursion and remainder control; this module handles the first comparison and does not assume that continuation.

Let `M` be a valid finite discounted MDP, π any fixed stationary randomized policy, `γ=M.discount`, `V=M.trajectoryExpectedValue π` the **actual infinite-trajectory** true value, `P=P_π`, `P̂=P̂_π(data)` the actual sampled empirical policy kernel, `R=(I−γP)⁻¹`, and `R̂=(I−γP̂)⁻¹`. The integrated true and empirical inverse modules prove both matrix inverses exist. Define

```text
σ(s) = Var_{P(s)}(V),   u = R sqrt(σ),   û = R̂ sqrt(σ).
```

`trueVarianceResolvent M π` is u; it depends on the fixed true model and π, not the random data. `empiricalVarianceResolvent M π N hN data` is û; only the empirical resolvent depends on data. The actual experiment is `ModelBasedPolicyEvaluation.samplingLaw M π N`, which draws N independent next states from each fixed true policy row. π is fixed before sampling.

## Deterministic identities and bounds

All exports are under `StatisticalRL.ModelBasedPolicyEvaluation`.

- `empirical_true_resolvent_identity` proves for **every** state vector f and every data outcome the literal finite-matrix identity

  ```text
  R̂ f − R f = γ R̂ (P̂−P) R f.
  ```

  It uses the separately proved true and empirical invertibility, not a formal inverse supplied as an assumption. This is the exact source comparison with the correct orientation and sign.
- `empirical_resolvent_norm_le` proves `‖R̂ f‖∞≤‖f‖∞/(1−γ)` from the actual empirical stochastic rows and the discount contraction. `empirical_true_resolvent_norm_le` combines that with the identity, obtaining

  ```text
  ‖R̂ f − R f‖∞ ≤ γ/(1−γ) ‖(P̂−P)R f‖∞.
  ```

  This is a deterministic, valid but coarse norm bound. No residual concentration event is an input to these declarations.
- `trueVarianceResolvent_nonneg` proves u is pointwise nonnegative for `γ>0` using the actual true-resolvent square-root budget. `empirical_true_resolvent_eq_of_zero` separately covers the endpoint: when γ=0, both resolvents act identically on every f.

## Unconditional Bernstein comparison

For `N>0`, `0<δ<1`, `γ>0`, and `S=card State`, define the fixed true-model radius vector

```text
L = log(4S/δ),
r_s = sqrt(2L/N) sqrt(Var_{P(s)}(u)) + 2‖u‖∞ L/(3N).
```

`trueVarianceResolventBernsteinRadius_eq` proves this literal source radius from the existing single-row Bernstein family radius at δ/S. `trueVarianceResolvent_residual_bernstein` proves, under the **actual sampling law**, that with probability strictly greater than `1−δ`, for all states,

```text
|[(P̂−P)u](s)| ≤ r_s.
```

It derives the event from the independently reviewed fixed-family source Bernstein theorem applied to `{u}`, the actual iid policy-row marginal of the global experiment, and a finite union bound. u is a fixed true-model vector and is proved nonnegative; no data-independence or unexplained concentration event is added as a theorem premise. The source's exact coefficient 2, denominator 3N, and log factor 4S/δ are retained. The empirical and true transition rows may coincide or have zero-probability states; zero variance and zero vectors are covered by the imported Bernstein result.

`empirical_true_varianceResolvent_bernstein` combines this event with the deterministic norm comparison:

```text
P(‖û−u‖∞ ≤ γ/(1−γ) ‖r‖∞) > 1−δ.
```

Finally `empirical_varianceResolvent_scaled_bernstein` applies the reviewed true-resolvent square-root bound and triangle inequality on the same derived event:

```text
P(γ ‖û‖∞ ≤ ‖V‖∞/sqrt(1−γ) + γ²/(1−γ) ‖r‖∞) > 1−δ.
```

The second term contains the true higher-order variances `Var_P(u)`, exactly the type of residual the source's recursive analysis must handle. The theorem does **not** bound it by an assumed sharp rate, identify an arbitrary data-dependent vector as independent, or close the multilevel recursion. The positive-γ premise is used to prove u nonnegative for the imported Bernstein theorem; the separate zero-discount identity covers γ=0 at the deterministic comparison level, not a separate probability statement.

## Verification, identity, and remaining work

The exact staged source was copied unchanged to a temporary probe with nine appended `#print axioms` commands and compiled using `bash scripts/lean-local.sh` against the integrated evaluation/inverse/true-resolvent/Bernstein artifacts. It compiled without diagnostics. `empirical_true_resolvent_identity`, `empirical_resolvent_norm_le`, `empirical_true_resolvent_norm_le`, `trueVarianceResolvent_nonneg`, `empirical_true_resolvent_eq_of_zero`, `trueVarianceResolventBernsteinRadius_eq`, `trueVarianceResolvent_residual_bernstein`, `empirical_true_varianceResolvent_bernstein`, and `empirical_varianceResolvent_scaled_bernstein` each use only `propext`, `Classical.choice`, and `Quot.sound`. This is a focused staged check, not a project integration build.

The remaining source work includes the full sequence of auxiliary values/variance radii, joint probability over all required levels, contraction/geometric recursion and terminal term, and explicit constants/sample arithmetic for `thm:model-based-policy-eval`. The bound here uses the generic `1/(1−γ)` empirical-resolvent norm, so it does not itself recover the source horizon-three rate. Independent source/semantic review and integrated export/axiom checks are required.

SHA-256:

- `.local/PolicyEvaluationEmpiricalResolvent.lean`: `2ad672efe62e102cdf654f95446fd884a4c9c0ab64b30b2cc38708ff205489a4`.
- `Formalization/Generative/PolicyEvaluationInverse.lean`: `d99f9b37bead6b7643377f8fd5572c4c18cf375ff1c6879e6889f0870b91cfc9`.
- `Formalization/Generative/PolicyEvaluationVarianceResolvent.lean`: `d971ae8c37d878fc3a64ed10f0c87ec4a9883abc6c2c210d6492b9e7bbe734de`.
- `Formalization/Generative/PolicyEvaluationHoeffding.lean`: `95779576e3078fbc7bd44c0e3d774e1abca99dd24fdaa2f622cf5d1b2975da3e`.
- `Formalization/Generative/ModelBasedPolicyEvaluation.lean`: `fe368676ff1a9b30b988112ae3478b3ed46abf1949c66a2169751fb60560aa53`.
- `Formalization/Probability/BernsteinFamily.lean`: `3f3d25c0953b629e7a8fba0921edf9a689a9818606e99e8eca7e64306299bcfe`.
- Source `generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.
