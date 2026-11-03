# All-row fixed-grid Bernstein event

Source: `source/upstream/tex/chapters/generative_model_model_based.tex:1305–1311, 1325–1342`, `eq:beta-policy-learning` and `eqn:bernstein-union`; source SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

`.local/PolicyLearningAllRowBernstein.lean` proves, for every finite valid MDP, `N>0` and `0<δ<1`, that the **actual** joint generative sampling law assigns probability strictly greater than `1−δ/2` to one event on which all states `x`, actions `a`, and fixed grid indices `i : Fin(N+1)` satisfy

```text
|(P̂_{x,a} − P_{x,a}) W_{x,i}| ≤
  √(β₁/N) √Var_{P_{x,a}}(W_{x,i}) + β₁/(3N(1−γ)),
β₁ = 2 log(16 S A N / ((1−γ) δ)).
```

`W_{x,i}` is the actual optimal infinite-trajectory value of the x-absorbing **empirical** MDP at the fixed source grid parameter `i/[N(1−γ)]`. `leaveOneOutGridValue_eq_gridValue` identifies this vector definitionally with the independently reviewed grid module's `absorbingGridValue` for the actual empirical model, so the later cover theorem applies to the same objects. The exact source logarithm, variance under the true row, `1/3` coefficient and strict joint probability are retained. There is no assumption of the desired good event or concentration inequality.

For each row, the proof applies the reviewed one-row fixed-family Bernstein result with `η=δ/(2SA)`. It proves the actual family image has `1≤k≤N+1`, even without assuming all index images distinct, then uses the reviewed grid log inequality `2log(4k/η)≤β₁`, actual-trajectory value norm `≤1/(1−γ)`, and nonnegative square-root comparison to dominate the exact random-family radius. It unions the `SA` row failures, each strictly less than η, and complements the measurable finite union. No independence among rows' families and no family independence from the whole transition matrix is assumed; the only statistical independence consumed is the previously proved off-state code versus its own removed row.

The resulting event is already universal in every grid index. A data-dependent covering index may later be selected **after** the event is fixed, without asserting that selected index or vector is independent. This file does not itself select that index, transfer to the full empirical optimal value, prove the standard-deviation perturbation lemma, or establish the later self-bounding policy-learning theorem. It includes `N=1` and `γ=0`; `N=0` is excluded by empirical frequencies.

Validation: rebuilt unchanged reviewed staged dependencies `PolicyLearningLeaveOneOutBernstein.lean` and `PolicyLearningAbsorbingGrid.lean` to project-owned `.local` oleans, then `lake env bash -c 'export LEAN_PATH="$PWD/.local:$LEAN_PATH"; lean .local/PolicyLearningAllRowBernstein.lean'` passed without diagnostics. An exact-source temporary probe checked grid-value identification, family cardinal bounds, radius domination, and the all-row event; all four reported only `propext`, `Classical.choice`, and `Quot.sound`. Source SHA-256 `c28ab6963d52be915aedc7909d6ad6c894bf6666e0cb9312f33a45ce67dc1189`; staged one-row dependency `9d31d1e0baf81e453c7eea903b6b0c62dd27db126895a0a0ad887c17760546b5`; staged grid dependency `9eb3bb60ee40b35f5c3fb378c1db43edc0d1648d1d230c0b06b5be028063e9ef`; staged one-row's independence dependency `11e3898042467a80949638d14f1499743fa274412e0a7774d5bb5731ac952abf`. Source/semantic independent review and validation of the production export remain outstanding.
