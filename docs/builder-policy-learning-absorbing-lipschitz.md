# Fixed-parameter absorbing-value stability

Source: `source/upstream/tex/chapters/generative_model_model_based.tex:1273–1302, 2620–2628`, especially `LemValueCover` and `eq:loo-value-cover`; source SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

`.local/PolicyLearningAbsorbingLipschitz.lean` proves the source's deterministic stability ingredient. For any admissible finite discounted MDP, state `x`, and fixed `u,v∈[0,(1−γ)⁻¹]`, its actual absorbing-model optimal trajectory values satisfy

```text
‖V*_{x,u} − V*_{x,v}‖∞ = |u−v|.
```

The upper bound derives from the two models' identical transition rows and their reward difference bounded by `(1−γ)|u−v|`: the Q-Bellman contraction and uniqueness bound the actual optimal Q fixed-point difference by `|u−v|`, then finite action-maximum nonexpansiveness transfers this to optimal state values. The reverse bound follows because the true trajectory value at the absorbing state is precisely `u` or `v` for every stationary policy. Equality is stronger than the source's required Lipschitz inequality and includes `γ=0`.

This is a deterministic fixed-parameter result, not a leave-one-out independence theorem, net existence proof, or the entire source value-cover lemma. It makes no independence claim for parameters selected using the removed samples. Combining it with the independently staged source preservation identity and a deterministic finite grid is a separate step.

Validation: unchanged staged absorbing preservation was built with `lake env bash -c 'export LEAN_PATH="$PWD/.local:$LEAN_PATH"; lean -o .local/PolicyLearningAbsorbingPreservation.olean .local/PolicyLearningAbsorbingPreservation.lean'`. Then `lake env bash -c 'export LEAN_PATH="$PWD/.local:$LEAN_PATH"; lean .local/PolicyLearningAbsorbingLipschitz.lean'` passed without diagnostics. Exact-source temporary axiom probes of the Q bound and actual-value equality reported only `propext`, `Classical.choice`, and `Quot.sound`. Staged source SHA-256 `41f647e9c3c10253eb78a1089f22def29460b4452149e3b6bd5c3a0a9684f86e`; staged preservation dependency `f30ea6939c2f18a913321da758575a13d023241ec8ff19c174e899bcb3cc034b`; staged absorbing dependency `dfdedc125e606f88241c2c491df64306ee3b0b2f83b6361f5f9dcaa6b2bd0a92`. Independent source/semantic review and integrated-export validation remain outstanding.
