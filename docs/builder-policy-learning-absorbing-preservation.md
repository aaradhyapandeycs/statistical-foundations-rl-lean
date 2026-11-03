# Absorbing-model optimal-value preservation

Source: `source/upstream/tex/chapters/generative_model_model_based.tex:1226–1272`, `LemAbsToNormalV` / `eqn:relation`, with proof at lines 2590–2619; source SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

`.local/PolicyLearningAbsorbingPreservation.lean` proves the source's exact identity for every admissible finite discounted MDP, each state `x` and each state `s`:

```text
V*_{x,V*(x)}(s) = V*(s),
```

where both sides are the actual infinite-trajectory state values of their respective deterministic optimal greedy policies. The absorbing model is exactly the independently reviewed fixed-parameter construction in `.local/PolicyLearningAbsorbing.lean`; the actual original optimal value's built-in trajectory bounds prove its parameter is admissible. No preservation equality is assumed.

The proof constructs the absorbing model's candidate optimal Q: it equals the old optimal Q away from `x` and is constantly `V*(x)` over actions at `x`. The maximum of this candidate is the original actual optimal value at every state. Substituting that continuation into the absorbing optimal-Q Bellman operator gives equality at `x` by absorption and `(1−γ)V*(x)+γV*(x)=V*(x)`, and away from `x` by the original optimal-Q equation. Uniqueness of the project's optimal-Q fixed point identifies the candidate with the absorbing model's actual optimal Q; the actual greedy-trajectory/value bridge then yields the state-value identity. This avoids the invalid stronger claim that the original Q table itself stays unchanged at the absorbing state.

The empirical corollary applies this result **pointwise to every actual sampled empirical MDP** and identifies the original empirical optimal trajectory value with `valueEstimator`; the parameter is the empirical optimal value at `x`. This pointwise identity does not imply independence: the chosen parameter can depend on the omitted state samples, exactly as the source warns. The finite net and measure-theoretic decoupling remain open. The result does not prove any policy-learning concentration or sample-complexity theorem.

Validation: `bash scripts/lean-local.sh -o .local/PolicyLearningAbsorbing.olean .local/PolicyLearningAbsorbing.lean` rebuilt the unchanged reviewed staged dependency; `lake env bash -c 'export LEAN_PATH="$PWD/.local:$LEAN_PATH"; lean .local/PolicyLearningAbsorbingPreservation.lean'` passed without diagnostics. An exact-source temporary probe of the general preservation theorem and the empirical estimator corollary reported only `propext`, `Classical.choice`, and `Quot.sound`. Preservation file SHA-256 `f30ea6939c2f18a913321da758575a13d023241ec8ff19c174e899bcb3cc034b`; absorbing dependency SHA-256 `dfdedc125e606f88241c2c491df64306ee3b0b2f83b6361f5f9dcaa6b2bd0a92`. Independent source/semantic review and production-export validation are outstanding.
