# One-row Bernstein for a fixed auxiliary family

Source: `source/upstream/tex/chapters/generative_model_model_based.tex:1273–1290, 1334–1344`, especially `eqn:bernstein-union`; source SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

`.local/PolicyLearningLeaveOneOutBernstein.lean` proves a one-row, actual-law Bernstein event for any fixed finite indexed family of admissible absorbing parameters. For state `x`, action `a`, positive sample count `N`, and `0<δ<1`, it builds the actual finite set of **distinct** fixed-parameter auxiliary optimal trajectory-value vectors using only the off-state code. With probability strictly greater than `1−δ` under the genuine product sampling law, every vector `V` in that family satisfies the existing exact population-Bernstein bound

```text
|(P̂_{x,a}−P_{x,a})V| ≤ bernsteinRadius(P_{x,a}, N, k, δ, V),
k = number of distinct vectors in the actual off-state family.
```

The family cardinality is proved at most the number of parameter indices; duplicates are not ruled out. Empty families are supported and yield a vacuous event. A separate corollary states that the same event controls every fixed parameter index simultaneously, identifying each off-state-completed vector with the actual auxiliary value vector by the previously proved factorization. A later data-dependent index may be selected **after** this event is established; the corollary does not claim that selected index or selected vector is independent of the row.

The proof consumes the staged off-state code's measurability and genuine independence from the actual empirical frequency row, the actual row sample law from `PolicyLearningHoeffding`, and the existing code-level random-family Bernstein theorem. It explicitly derives nonnegativity from actual infinite-trajectory reward bounds and verifies the finite-code measurability assumptions. It does not assume the family is independent of the entire transition matrix, nor independence between its members.

This is **one row**, not the source's simultaneous all-state/action event. A union over all rows, the explicit source logarithm/constant comparison, a particular `N+1`-point grid, its net approximation and the final policy-learning rate remain separate. No author-frozen theorem or source-theorem completion is claimed.

Validation: rebuilt the unchanged staged independence dependency using `bash scripts/lean-local.sh -o .local/PolicyLearningLeaveOneOutIndependence.olean .local/PolicyLearningLeaveOneOutIndependence.lean`, then `lake env bash -c 'export LEAN_PATH="$PWD/.local:$LEAN_PATH"; lean .local/PolicyLearningLeaveOneOutBernstein.lean'` passed without diagnostics. An exact-source temporary probe checked the family cardinality bound and both probability results, with only `propext`, `Classical.choice`, and `Quot.sound`. Staged Bernstein SHA-256 `9d31d1e0baf81e453c7eea903b6b0c62dd27db126895a0a0ad887c17760546b5`; staged independence dependency `11e3898042467a80949638d14f1499743fa274412e0a7774d5bb5731ac952abf`; integrated `BernsteinFamily.lean` `3f3d25c0953b629e7a8fba0921edf9a689a9818606e99e8eca7e64306299bcfe`; integrated `PolicyLearningHoeffding.lean` `b30bd558ad8f2e7d708b89b8541509e4616c508d0d77d0b8f9539e7a59b9912a`. Independent source/semantic review and production-export validation are outstanding.
