# Conditional auxiliary residual recursion

Source: `source/upstream/tex/chapters/generative_model_model_based.tex` lines 461–495, `eq:Vl-Vhat-l-perturbation` and steps (i)–(iii) of `eq:upper-bound-Vl-Vhatl`; source SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

`.local/PolicyEvaluationResidualRecursion.lean` proves the exact empirical-minus-true auxiliary resolvent identity for every level and every sample. It then proves the following **conditional deterministic helper**, for nonnegative coefficients `a,c` and any particular sample satisfying the explicitly stated pointwise input

```text
|(P̂−P)V_l|(s) ≤ a √Var_{P(s)}(V_l) + c ‖V_l‖∞,  for every s:

‖V̂_l−V_l‖∞ ≤ γ a (‖V̂_{l+1}−V_{l+1}‖∞ + ‖V_{l+1}‖∞)
                  + γ c ‖V_l‖∞/(1−γ).
```

The proof applies the actual empirical inverse's absolute-value domination, monotonicity, and exact row sum, then the triangle inequality. It consumes the pointwise residual bound and both nonnegative coefficient hypotheses. All vectors and matrices are the actual policy-evaluation constructions; the helper is valid at γ=0 and makes no probability or independence claim.

The prior staged simultaneous Bernstein event is a potential source of this rowwise hypothesis, but this file does **not** connect that event to the helper or prove a high-probability recursion. Nor does it prove the source's sharper step (iv), which requires a separately established sharp variance-resolvent bound for every auxiliary vector. It does not prove the final policy-evaluation theorem. The source-selected positive-discount choice of `m` is at least two; the logarithm comparison is described in `docs/builder-policy-evaluation-recursion-plan.md`.

Validation: compiled `.local/EmpiricalResolventOrder.lean` to a staged `.olean`, then used `lake env bash -c 'export LEAN_PATH="$PWD/.local:$LEAN_PATH"; lean .local/PolicyEvaluationResidualRecursion.lean'` with the unchanged staged auxiliary `.olean`. A separate exact-source axiom probe for both declarations reported only `propext`, `Classical.choice`, and `Quot.sound`. The staged file deliberately imports `PolicyEvaluationAuxiliary` and `EmpiricalResolventOrder`; integration must change those imports to the reviewed production paths and validate the actual exports. The compiled staged auxiliary and inverse-order dependency sources have SHA-256 `68a6bc19097ecc84a93583a39230b92b58b4a3ab8a2c0971ab50d084923bbb95` and `bed62174679d0a11f0778702e29f77a004d144a26d5e8f5b4661644ffafd0bf5`; the recursion file is `860c81d21b55b58df3b9eefe66c341ee3a60f7edd9cfd67c66e1b089be0c8c4d`. Independent source and semantic review remains outstanding.
