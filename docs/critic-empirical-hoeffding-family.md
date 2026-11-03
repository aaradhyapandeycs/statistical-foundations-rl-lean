# Independent review: deterministic finite-family Hoeffding bound

**Verdict: PASS for the stated deterministic finite-family specialization, including the exact source radius and strict success probability.** The source lemma's random finite family independent of the empirical row remains unproved. This is a scoped ordinary review, not an author-approved frozen-declaration audit or closure of Lemma 2.4.

The reviewer did not author the staged family module. I reconstructed the raw-source statement before inspecting its code, and examined the already-integrated empirical sampling and fixed-vector Hoeffding dependencies. The latter had a separate independent review in `docs/critic-empirical-hoeffding.md`.

## Source and scope

`source/upstream/tex/chapters/prelim.tex:916–927` defines N iid draws from a given transition row and the empirical-frequency row. Lines 939–949, `lem:Hoeffding-prelim`, gives for `0 < δ < 1` a simultaneous bound over a finite family `𝒱 ⊆ ℝ_+^S` independent of that row, with probability **strictly greater** than `1−δ` and exact threshold

```text
sqrt(‖V‖∞² log(2 |𝒱| / δ) / (2 N)).
```

A fixed deterministic family is a valid specialization of the source's independence setting, but does not cover random families. The staged theorem requires `N>0`, necessary to form the normalized empirical distribution as implemented; the displayed source does not explicitly spell out N positivity. Its main strict theorem also requires a nonempty family, necessary for its logarithmic cardinality algebra. Empty families are handled separately as a vacuous probability-one event. Because the paper's expression involves `log |𝒱|`, its literal empty-family convention still needs to be made explicit in a full source-facing transcription; Lean's total real logarithm at zero is not itself an author ruling.

## Model, radius, and proof

- `EmpiricalRow.lean` constructs `sampleMeasure N` as the actual product of N copies of the true row measure, establishes independent coordinate sampling, and defines empirical frequencies for `N>0`. `empiricalRow_expectation` is the sample average and the row mean is the genuine finite expectation. Thus the family theorem is on the right data-generating law, not an arbitrary measure with a concentration assumption.
- The input `d : FiniteDistribution State` expands to a normalized nonnegative finite transition row; `State` is finite. `family : Finset (State → ℝ)` is fixed before sampling, `hV` gives source nonnegativity for every member and state, and `δ` has exactly the source open-interval bounds. No pre-assumed family tail estimate, empirical-row independence, fixed-point, or random-family property is hidden in the theorem inputs.
- `familyRadius_eq_source` proves the auxiliary `‖V‖ * sqrt(log(2k/δ)/(2N))` equals the source's square-root expression with the **same** `k`, N, δ and `‖V‖`. The finite Pi norm is the supremum of absolute state coordinates. Source nonnegativity makes each sample fall in `[0,‖V‖]`, which is essential to the factor `2N` in the exponent. For positive norm the imported fixed-vector theorem has exactly `2 exp(−2Nε²/‖V‖²)`; for zero norm, `empiricalRow_norm_zero_deviation` makes the deviation identically zero, avoiding any division by zero.
- `familyViolation_lt` correctly obtains a **strict** per-vector failure bound. If the strict failure set is empty, its measure is zero while `δ/k>0`. Otherwise the sample carrier `Fin N → State` is finite, so the finite nonempty set of *all* violating sample outcomes has an attained minimum deviation m strictly larger than the radius, irrespective of zero-probability outcomes. Every violation lies in the closed tail at m. The fixed-vector Hoeffding bound there is strictly less than its value at the radius: N and `‖V‖` are positive, m exceeds the nonnegative radius, and real exponential is strictly increasing. The radius algebra evaluates the latter bound to `δ/k`. It does not infer a strict probability from the non-strict tail bound alone.
- `empiricalRow_family_success_gt` takes a finite union bound, then uses a strict finite sum over the **nonempty** family and complements the measurable failure event. Consequently its conclusion is genuinely `1−δ < P(success)`, with the source's `≤` event for every V. The fixed-vector and union steps cover every V simultaneously with one sample, not a separately chosen sample per vector. The additional `_success_ge` result is a weaker helper, not a substitute for the strict theorem.
- `empiricalRow_empty_family_success` proves the universal event for an empty deterministic family has probability 1, for any δ. This is valid as a vacuous event and requires no positivity or fabricated member. It does not by itself settle the paper's intended mathematical definition of the displayed logarithmic expression for an empty family.

## Exact evidence

Reviewed SHA-256 values:

| File | SHA-256 |
| --- | --- |
| `.local/EmpiricalHoeffdingFamily.lean` | `0b8bf547984a749623012f9a6a19ffe92ffa9c10f8a69d6b4abf139c794dc12d` |
| `Formalization/Probability/EmpiricalHoeffding.lean` | `fd8be9002c7e5c6e418461818e7842c96520ca604e10e466f8431b1307798b55` |
| `Formalization/Probability/EmpiricalRow.lean` | `6e87c90ff1150f7053845acff92d60a5c35035c7a78adcd394e0da5f3d9dc154` |
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` |

A temporary copy of the exact staged source with independently appended probes compiled with `bash scripts/lean-local.sh <temporary-file>`. The probes prove the zero vector's violation event is exactly empty for every N, k, and δ, and instantiate the strict source-radius success theorem for the nonempty singleton family `{0}`. The same run checked `#print axioms` for `familyRadius_eq_source`, `familyViolation_lt`, `empiricalRow_family_success_gt`, and `empiricalRow_empty_family_success`; each reported only `propext`, `Classical.choice`, and `Quot.sound`. The temporary file was removed. This is a staged-source check, not a check of a later integrated module or a whole-project build.

## Remaining random-family obligation

The code quantifies over a deterministic `Finset`, not a random finite set depending on a larger probability space. To cover the source clause, define a measurable random finite set and its random cardinality, prove the event of simultaneous source-radius success is measurable, and use its **independence from the empirical row** to condition or use a product-law argument. The theorem must accommodate nonempty random cardinalities that vary across outcomes and the empty-family convention; independence from the entire ordered sample sequence would be stronger than the source's stated independence from the empirical row. The strict probability must survive the conditioning/mixture argument. No part of that generalization is established by this specialization alone.
