# Independent review: two-state lower-bound parameters

**Verdict: pass for the stated scalar parameter arithmetic.** This does not prove the source's two-MDP Q-gap lemma or minimax theorem.

The source `generative_model_model_based.tex:1728–1788`, labels `eq:choise-p-alpha-lower-bound-generative` and `lem:properties-M01-lower-generative`, chooses

    p=(4γ−1)/(3γ),    α=32(1−γ)²ε/(9γ²)

for `2/3≤γ<1` and `0<ε<1/[32(1−γ)]`. The staged definitions exactly use these expressions. The source's equivalent α expression `2(1−γp)²ε/γ²` is established inside the scalar-gap proof by `1−γp=4(1−γ)/3`. All denominators used in that proof are positive under the stated discount range, not assumed through totalized division.

`source_parameters_admissible` states precisely the source part (i): `1/2≤p<p+α<1` and `2α≤1−p`. It derives α>0 and in fact proves the last bound strictly before weakening it. Endpoints are handled faithfully: γ=2/3 is allowed, γ=1 and ε at its strict upper boundary are excluded, and ε>0 is explicit. These facts justify p and p+α as distinct valid Bernoulli probabilities.

`source_parameters_scalar_separation` proves the exact reciprocal inequality

    1/[1−γ(p+α)] − 1/[1−γp] > 2ε.

The source identifies this expression with its two constructed MDPs' actual optimal Q gap via `eq:Qstar-hard-instance-generative`; the staged theorem does not construct either MDP or prove that identification. It is therefore the arithmetic component of part (ii), not a complete formal proof of part (ii). The proof checks positivity of both Bellman denominators and preserves the source's strict `>2ε`.

`source_parameters_squared_ratio` proves exactly `α²/(1−p)=32²(1−γ)³ε²/(27γ³)≤128(1−γ)³ε²`. The numerical 128 follows from γ≥2/3, which gives `27γ³≥8`. This theorem uses only the weaker ε>0, not the source upper bound; that is a valid strengthening of the arithmetic statement. It proves the source part (iii), not the Bernoulli KL inequality that later consumes it.

The module contains no hypothesis encoding the desired admissibility, gap, or ratio as an input. It also contains no generative sampling experiment, estimator, Bernoulli KL, testing/Fano inequality, fixed-size embedding, or minimax probability conclusion. The two-state illustration has S=2 and A=1 and is separate from any claim about the disputed fixed-size all-model theorem. Later statistical lower-bound work must build the actual MDPs, establish actual trajectory Q semantics, and verify its own estimator/model quantifiers.

Staged source SHA-256 `fd1becc5650644ed0f39d3bbbba2eb10c1b467a61910c2afe2a929b4339f5121`; pinned source TeX SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. An exact unchanged source copy with original imports and five appended axiom checks compiled independently, exit 0. Both definitions and all three theorem exports use only `propext`, `Classical.choice`, and `Quot.sound`. Actual production export verification remains separate.

## Integrated export verification

Production `Formalization/Generative/GenerativeLowerBoundParameters.lean` is byte-identical to reviewed SHA-256 `fd1becc5650644ed0f39d3bbbba2eb10c1b467a61910c2afe2a929b4339f5121`. The actual module compiled and import-only checks of both definitions and all three theorems used only `propext`, `Classical.choice`, and `Quot.sound`.
