# Simultaneous Bernstein event for auxiliary values

Source: `source/upstream/tex/chapters/generative_model_model_based.tex` lines 471–480, `eq:Bernstein-Vl`, SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

`.local/PolicyEvaluationAuxiliaryBernstein.lean` proves, under the genuine policy-row product sampling law and for positive `N` and `0 < δ < 1`, a single event of probability strictly greater than `1−δ` on which every state and every `0 ≤ l ≤ m` obeys

```text
|(P̂π−Pπ)V⁽ˡ⁾|(s)
  ≤ sqrt(2 L / N) sqrt(Var_{Pπ(s)}(V⁽ˡ⁾))
    + 2 ‖V⁽ˡ⁾‖∞ L / (3N),
L = log(4 |S| (m+1) / δ).
```

The empirical row and true policy row in this statement are the actual algorithmic rows. The family is the deterministic sequence defined from the true MDP; the proof applies the fixed-vector row Bernstein bound to each pair `(s,l)` and takes a finite union. It never assumes that different levels are independent. The explicit `m+1` counts the source's stated inclusive range `0≤l≤m`; its informal `log(Sm/δ)` can be compared up to constants only with an appropriate restriction on `m` and chosen universal constant. The bound above is stronger than the source-shaped form with `β₁=2L` in its linear coefficient, subject to the usual nonnegativity arithmetic.

This is the concentration event only. It does not prove the auxiliary value growth bound at the source's sharp rate, the resolvent comparison, the recursive bound, or the final sample theorem. It imports the unchanged staged `PolicyEvaluationAuxiliary.lean`, which still requires its own independent source review. No integrated-export claim is made.

Validation: first `bash scripts/lean-local.sh -o .local/PolicyEvaluationAuxiliary.olean .local/PolicyEvaluationAuxiliary.lean`, then `lake env bash -c 'export LEAN_PATH="$PWD/.local:$LEAN_PATH"; lean .local/PolicyEvaluationAuxiliaryBernstein.lean'`. Both passed. A separate exact-source probe of `auxiliaryValues_bernstein_explicit` reported only `propext`, `Classical.choice`, and `Quot.sound`. Staged event file SHA-256 `2a4a6df841a284b0db5a1b157d2240ee43e60ed060bd3b81bb47b03c95da3671`; staged dependency SHA-256 `68a6bc19097ecc84a93583a39230b92b58b4a3ab8a2c0971ab50d084923bbb95`. Independent review remains outstanding.
