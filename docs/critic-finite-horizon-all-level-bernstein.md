# Independent review: all-level finite-horizon Bernstein event

Reviewed `.local/FiniteHorizonAllLevelBernstein.lean`, SHA-256 `49350c3a7f8c26a2cce3b53ef29ba902d34eef7b70476d32e8fb81dd6fe11c0c`, together with the causal selector source `.local/FiniteHorizonFittedAuxiliaryContinuation.lean`, SHA-256 `371608d6edb5deca0c6f2da377d28e3e5a43883453593f228dd3fb56da1b638a`. This is an independent source/semantic review and fresh compile/axiom check of the staged closure; production integration was not checked.

## Conditional row bound and causal scope

`futureValue_row_bernstein` applies the actual random-family Bernstein theorem to the singleton family containing the selected vector. The vector is pointwise nonnegative and, by its explicit factorization premise, is a function only of strictly future data. The sampling law is the actual product experiment; `futureData_indep_row` and composition with the measurable empirical-row map establish independence from the current row, while `samplingLaw_row` supplies the actual iid row marginal. The theorem adds no independence hypothesis or false assumption that a data-selected vector is independent of its own observations.

For the fitted branch, the selector is the fixed `backwardGreedyActions` recursion using `EnvironmentStage.greedyAction` and the recursively optimal empirical suffix. `greedyAction` uses a fixed `Classical.choose` maximizer, so ties are deterministically resolved as a function of that empirical stage and suffix. The suffix/drop identity removes the current stage and all earlier stages before the continuation is evaluated at `h+1`. Thus the post-current-stage fitted true auxiliary continuation depends only on strictly future empirical stages. The action selected at the current stage may still depend on current rows; the simultaneous event covers every action and can therefore be used after the action is selected. Arbitrary globally data-selected optimizers with noncausal tie rules are not covered by this draft.

The second branch of `sourceAuxiliaryContinuation` is any fixed policy function, independent of data, and factors through future data trivially. Its signature does not assume that `fixed` is optimal; the theorem is valid for any such fixed function and can be instantiated with the source's true-optimal policy. Both branches are nonnegative. The event's Bool index chooses between these two continuation families, not a randomized policy.

## Union size, confidence, radius, and endpoints

With `K=Nat.log 2 H+1` and `I=Fin H × State × Action`, the index set is `Bool × Fin K × I`, of cardinality exactly `2*K*H*|State|*|Action|`. The proof derives nonemptiness of `Fin H`, state, action, and `Fin K` from `hH>0`, the first environment's witnesses, the explicit fallback action, and `K>0`. It allocates `η=δ/card(J)`, proves every bad event has measure `<η` from the row theorem's strict `1−η` success probability, and uses finite union bound to get union measure `<δ`. Taking the complement gives the exported strict `1−δ` probability. The displayed per-row confidence is exactly `δ/(2*K*|I|)`.

The row radius has family-cardinality factor one because the family passed to the conditional random-family theorem is a singleton. With `η=δ/(2KT)`, where `T=H|State||Action|`, its logarithm is `log(4/η)=log(8KT/δ)`. This is the conservative coefficient stated in `docs/source-finite-horizon-all-level-bernstein-plan.md`; it is not silently identified with the paper's smaller displayed intermediate logarithm. The plan reserves logarithm absorption and small-horizon branches as later obligations.

`N>0` is required to define empirical rows. `H>0` supplies actual stages. The all-level coordinate ranges over `Fin (Nat.log 2 H + 1)`, i.e. all natural levels `0,…,Nat.log 2 H`, exactly the floor-depth range consumed by the deterministic Lemma 9 wrapper. At `H=1`, the only level is zero and `h+1` is the terminal suffix; both continuation families are zero there, so the event remains valid. `H=0` is intentionally excluded because there is no `h : Fin H`.

## Fresh compile and axiom evidence

I freshly compiled the exact staged `FiniteHorizonAuxiliaryVariance`, `FiniteHorizonFittedAuxiliaryContinuation`, and `FiniteHorizonAllLevelBernstein` sources, in that order, to `.local/finite-all-level-review/`, then compiled an import-only probe of all ten fitted-continuation exports and all six all-level event exports. All compiles succeeded with no diagnostics. All 16 queried declarations reported exactly `propext`, `Classical.choice`, and `Quot.sound`.

The checked staged dependency hashes were variance `19f843f138314e21a14d5b29eef88e758add4389dbbcfa7eb225e496bc68d4ee` and fitted continuation `371608d6edb5deca0c6f2da377d28e3e5a43883453593f228dd3fb56da1b638a`; target hash is given above. The build used Lean 4.27.0-rc1 and existing pinned production/Mathlib artifacts. No dependency packages were rebuilt. The source plan describes the later common-event/Lemma 9 assembly but is not itself a completed source probability theorem.

**Verdict:** the causal continuation scope, deterministic tie handling, action-uniform union, strict confidence arithmetic, radius, and natural-level endpoints are consistent. The result supplies one actual-law event for the two stated continuation families; it does not by itself prove the downstream Lemma 9 residuals, fitted-policy evaluation error, or final H³ theorem.

Production integration: the corresponding production module bodies match the independently reviewed staged sources, with qualified imports. The full project export compiled and audited 2,522 declarations, permitting only `propext`, `Classical.choice`, and `Quot.sound`.
