# Independent review: all-row fixed-grid Bernstein event

**Verdict: pass for the stated all-row event.** This corresponds to the grid concentration step `eqn:bernstein-union` in `generative_model_model_based.tex:1305–1344`, not the later selected-value transfer or policy-learning theorem.

For each admissible finite MDP M, N>0, and `0<δ<1`, the proposed event under the actual joint state-action product sampling law quantifies simultaneously over every state x, action a and index `i : Fin(N+1)`. It bounds the actual empirical-minus-true row expectation of the actual x-absorbing empirical optimal trajectory-value vector by

    √(β₁/N) √Var_{P(x,a)}(W_{x,i}) + β₁/(3N(1−γ)),
    β₁ = 2 log(16 S A N / ((1−γ)δ)).

This is the source β, population variance row, 1/3 coefficient and inclusive source grid. `leaveOneOutGridValue_eq_gridValue` is definitional equality to the grid module's actual `absorbingGridValue` of the **same empirical model and data**; it does not substitute a different sampled model or a true optimal value. The norm bound is derived from the actual absorbing MDP trajectory-reward bounds.

For each fixed row the proof applies the reviewed one-row theorem with `η=δ/(2SA)`, whose family is built from off-state data and is independent of that row under the product law. The family is a finite image and its actual cardinal k can be strictly smaller than N+1 when value vectors coincide. The explicit cardinal lemma proves `1≤k≤N+1` without assuming injectivity; nonemptiness uses index zero. The imported grid-log comparison bounds `2 log(4k/η)` by β₁, and the proof uses nonnegative square roots and `‖W‖∞≤1/(1−γ)` to enlarge the exact random-family radius to the source radius with the same N and h.

The proof then forms one bad event per state-action row and unions exactly SA events. Each has probability strictly less than η. Finite State and Action are nonempty from M, so the strict finite sum gives total failure `<δ/2`; finite sample discreteness supplies measurability for complement and union. The resulting single event has probability `>1−δ/2`, which is stronger than the printed at-least statement. It does not assume independence between row events or independence of any auxiliary family from the full transition matrix.

Every grid index is controlled **before** any data-dependent selection. The file does not itself select a covering index or claim that the selected index/value is independent. It admits N=1 and γ=0; its positive N hypothesis is required for the grid and empirical rows. The reviewed source grid's separate cover/preservation dependencies must be retained; this module's `rfl` object identification is not a new proof of their semantics.

Remaining work includes the empirical-optimal-value grid cover, the standard-deviation transfer and source β≥4 arithmetic, selection of empirical greedy actions after the simultaneous event, and the source self-bounding resolvent/sample theorem. No complete policy-learning result is claimed here.

Staged source SHA-256 `c28ab6963d52be915aedc7909d6ad6c894bf6666e0cb9312f33a45ce67dc1189`; staged grid `9eb3bb60ee40b35f5c3fb378c1db43edc0d1648d1d230c0b06b5be028063e9ef`; staged one-row `9d31d1e0baf81e453c7eea903b6b0c62dd27db126895a0a0ad887c17760546b5`; staged independence `11e3898042467a80949638d14f1499743fa274412e0a7774d5bb5731ac952abf`. An exact unchanged source copy with its original imports and seven appended axiom checks compiled independently, exit 0, after the staged independence, one-row and grid dependencies were freshly rebuilt in an isolated project-owned directory. The two definitions and all five theorem exports use only `propext`, `Classical.choice`, and `Quot.sound`. Actual production import/export verification remains separate.

## Integrated export verification

Production `Formalization/Generative/PolicyLearningAllRowBernstein.lean` SHA-256 `2777c487b211e38a2eabccaa56f1656d4da5d345727884e6e42822bbc9f6ae2c` differs from the reviewed staged source only by qualification of its two staged imports. The actual integrated module compiled and an import-only audit of its two definitions and five theorem exports used only `propext`, `Classical.choice`, and `Quot.sound`.
