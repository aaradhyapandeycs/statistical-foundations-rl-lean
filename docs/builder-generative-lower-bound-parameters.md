# Two-state generative lower-bound parameter helper

Exact staged source `.local/GenerativeLowerBoundParameters.lean`, SHA-256 `fd1becc5650644ed0f39d3bbbba2eb10c1b467a61910c2afe2a929b4339f5121`; source-first plan `docs/builder-generative-lower-bound-parameters-plan.md`. This is independent of the disputed policy-learning Theorem 3.7 statement.

For the source choices p=(4γ−1)/(3γ), α=32(1−γ)²ε/(9γ²), and exact hypotheses 2/3≤γ<1 and 0<ε<1/(32(1−γ)), the staged code proves all three parts of the monograph's two-state parameter lemma (chapter lines 1728–1788): (i) 1/2≤p<p+α<1 and 2α≤1−p; (ii) the scalar reciprocal gap `1/(1−γ(p+α))−1/(1−γp)>2ε`; (iii) the exact ratio α²/(1−p)=32²(1−γ)³ε²/(27γ³) and ≤128(1−γ)³ε². Part (iii) is proved under the weaker assumptions 2/3≤γ<1 and ε>0. Denominator positivity and strict inequalities are proved; no conclusion-shaped premises are supplied.

The reciprocal gap is a scalar consequence, not a formal construction of the two MDPs or a proof of their actual trajectory Q values. The Bernoulli KL estimate, testing/Fano argument, and minimax probability conclusion remain open. Focused compilation of the exact staged file succeeded; axiom probes for both definitions and three theorems report only `propext`, `Classical.choice`, and `Quot.sound`. Independent source review and production-export validation remain.
