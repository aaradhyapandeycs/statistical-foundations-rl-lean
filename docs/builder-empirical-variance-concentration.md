# Empirical variance concentration: two-moment bound

The source empirical Bernstein lemma (`prelim.tex:983–998`, label `empirical bernstein`) bounds the actual empirical mean error using a random empirical-variance radius with sharp displayed constants, for `N≥2`, `0<δ<1`, and a finite independent family of nonnegative vectors. The general source lemma is **not proved** by this staged module.

I searched the pinned Mathlib probability and measure-theory sources for empirical Bernstein, sample variance concentration, bounded differences and McDiarmid results. The relevant available general concentration API located is the sub-Gaussian/Hoeffding machinery; no directly applicable theorem with the source's self-normalized radius was found in that local search. The existing project provides a genuine iid empirical row, its Hoeffding tail for bounded fixed vectors, and a deterministic comparison of empirical and true variances by the first and second empirical moments.

`.local/EmpiricalVarianceConcentration.lean` proves an unrestricted-in-confidence, fixed-vector intermediate result. For `N>0`, `B>0`, `ε≥0`, and `0≤V≤B`, under the actual iid law it establishes

```
P(|Var_P̂(V) − Var_P(V)| ≥ ε)
  ≤ 2 exp(−2N(ε/2)²/B⁴) + 2 exp(−2N(ε/(4B))²/B²).
```

It applies the existing Hoeffding result to `V²∈[0,B²]` and `V∈[0,B]`, uses the proved deterministic variance comparison, and takes the union bound. It also proves the same upper bound for the one-sided failure event `Var_P̂(V)+ε < Var_P(V)`, giving a valid data-dependent upper confidence bound on the population variance. The stated tail may exceed 1; no probability clipping is claimed. The result includes N=1 and ε=0, and needs B>0; a zero-range case would need separate handling. It assumes no empirical concentration, no final source inequality, and no external/custom axiom. The inequalities hold for every threshold rather than the earlier small-confidence condition.

The displayed bound has additive variance error of order `B² sqrt(log(1/δ)/N)`. Naively substituting it into the population-variance mean bound does not recover the source's sharp self-normalized constants or rate. The missing work is a sharper self-normalized empirical-variance concentration argument (or independently justified equivalent route), conversion to the exact source radius and strict success probability, and the simultaneous random finite-family extension under the source's independence hypothesis. No claim is made about the source lemma or its constants until those pieces are proved and independently audited.

Validation: `bash scripts/lean-local.sh .local/EmpiricalVarianceConcentration.lean` compiled cleanly. An exact temporary source copy with both appended `#print axioms` commands compiled and was deleted; `empiricalVariance_hoeffding` and `variance_upper_confidence_hoeffding` depend only on `propext`, `Classical.choice`, and `Quot.sound`. The first compiler run briefly overlapped a second worker after crossed coordination messages while the lead build was active; the overlap ended immediately when noticed. Subsequent checks were coordinated. Independent review and integrated export checks remain pending.

SHA-256:

- `.local/EmpiricalVarianceConcentration.lean`: `385479ab6a59961672c8eee4dac5d77b0bc265f636d685eeede10881dfc84bb8`.
- `Formalization/Probability/EmpiricalVarianceBernstein.lean`: `ac0d89639cdf3396e92dd4c3c7ca5be302952481ca1b8f68751b6dbadd9120c5`.
- `Formalization/Probability/EmpiricalHoeffding.lean`: `fd8be9002c7e5c6e418461818e7842c96520ca604e10e466f8431b1307798b55`.
- `source/upstream/tex/chapters/prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
