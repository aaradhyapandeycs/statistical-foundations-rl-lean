# Independent review: Bernoulli scalar divergence bound

**Verdict: pass for the scalar logarithmic expression and inequalities.** This is not yet an identification with measure-theoretic KL or a testing lower bound.

The source `generative_model_model_based.tex:1685–1710`, label `eq:KL-P1-P0-lower-generative-Q`, uses the directional divergence from Bernoulli `q=p+α` to Bernoulli p. The staged `bernoulliKLExpression q p` is exactly

    q log(q/p) + (1−q) log((1−q)/(1−p)).

For 0<p,q<1, both logarithm arguments and the denominator `p(1−p)` are strictly positive. The proof applies the actual pinned real inequality `log x≤x−1` to each ratio, multiplies by nonnegative q and 1−q, and verifies the exact algebraic result `(q−p)²/[p(1−p)]`. The orientation of the two parameters is correct; this scalar theorem does not rely on a reverse-KL identity.

The specialization assumes `1/2≤p`, `α>0` and `p+α<1`, from which it derives `0<p<1` and `0<p+α<1`, then uses `1/p≤2` to prove the source constant `2α²/(1−p)`. These are the parameter admissibility conditions established by the separately reviewed scalar parameter module. No conclusion-shaped hypothesis is introduced. Boundary distributions p=0, p=1, q=0 or q=1 are outside this theorem; the source hard-instance parameters are interior, so no unsupported boundary extension is needed.

The source also requires KL of the **actual** observed experiment in the direction `P₁‖P₀`, equality to N times the Bernoulli divergence, and then a statistical testing/Fano reduction. The staged definition is a real expression: its equality to a measure-theoretic KL, the contribution of the other deterministic row, product tensorization, estimator-to-test reduction and minimax probability statement are not proved here. In particular, multiplying this scalar inequality by N is algebraically immediate but is not by itself a proof of the experiment's KL identity.

Staged SHA-256 `e448cc57b89ace8b91fd65d0cd2a7999c17970e7c58381ff78de073488fe74f1`; source TeX SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. An exact unchanged source copy with original imports and three appended axiom checks compiled independently, exit 0. The definition and both theorems use only `propext`, `Classical.choice`, and `Quot.sound`. Actual production import/export verification remains separate.

## Integrated export verification

Production `Formalization/Generative/GenerativeLowerBoundBernoulli.lean` is byte-identical to reviewed SHA-256 `e448cc57b89ace8b91fd65d0cd2a7999c17970e7c58381ff78de073488fe74f1`. The actual module compiled and import-only checks of the definition and both theorems used only `propext`, `Classical.choice`, and `Quot.sound`.
