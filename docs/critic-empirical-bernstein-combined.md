# Independent review: combined empirical Bernstein bound

**Verdict: PASS for the stated fixed-vector observable empirical-variance confidence bound; the source's sharper random-family empirical Bernstein lemma remains unproved.** The staged result uses the actual iid empirical row and proves its displayed constants and probability bound. It has different constants/logarithm, a non-strict confidence probability, and no finite/random-family lift, so it must not be labeled the source theorem. This is a scoped independent review, not author approval or whole-paper completion.

Authoritative source: `source/upstream/tex/chapters/prelim.tex:916–927` for iid row sampling and empirical frequencies, `:427–443` for variance, and `:983–998`, label `empirical bernstein`, for the sharper empirical-variance result. The source requires N≥2, 0<δ<1, a finite nonnegative vector family independent of the empirical row, simultaneous success strictly greater than `1−δ`, radius involving `log(4|𝒱|/δ)/(N−1)`, and correction coefficient `7/3`. This staged result is correctly presented as a different, weaker-constant fixed-vector contribution.

## Inputs and actual observable quantity

Both target declarations are in `StatisticalRL.FiniteDistribution`. The sample law is `d.sampleMeasure N`, the actual N-fold product of the row measure, and `empiricalRow N hN ω` is the frequency distribution on the realized sample. `empiricalVariance N hN V ω` is the variance of V under that empirical row: `P̂(V²)−(P̂V)²`. It is the source's observable empirical-row variance, with 1/N frequency normalization; no true variance is present in the final radius. Its nonnegativity is proved in the imported variance infrastructure. The unknown true `d.variance V` appears only in the proof through the population-Bernstein and standard-deviation-tail intermediate events.

The theorem accepts a fixed, sample-independent `V : State→ℝ` satisfying `0≤V(s)≤B` for every state, `B>0`, N>0, and x>0. Its confidence corollary accepts `0<δ<1`. The choice `B=‖V‖∞` is available for nonzero nonnegative V; the zero vector is still included by supplying any positive B. The theorem does not permit B=0 in this declaration. N=1 is allowed; this is not claimed as the source N≥2 statement. The fixed vector and positive B are actual premises, not a quantified random family or hidden concentration assumptions.

## Events, probability, and constants

Writing `Z=Var_{P̂}(V)`, the exact strict failure event in `empiricalBernstein_combined_exp` is

```text
sqrt(2x/N) [sqrt(Z)+4B sqrt(x/N)] + 2Bx/(3N)
  < |(P̂−P)V|,
```

with probability at most `5 exp(−x)`. Thus equality with the radius is a success, and the bound is an **upper bound on failure**, not a strict success estimate. For N,x,B positive, the radius equals

```text
sqrt(2x/N) sqrt(Z) + (4 sqrt(2)+2/3) Bx/N.
```

This expansion is ordinary algebra; the Lean theorem prints the factored expression. The constant 5 is exactly the union of the imported population-variance strict-failure probability `≤2e^(−x)` and empirical-standard-deviation lower-tail probability `≤3e^(−x)`. No event independence is required. On the complement of the latter, the true standard deviation is at most `sqrt(Z)+4B sqrt(x/N)`; nonnegativity of the other square-root factor gives the event inclusion used in the code. The proof's square-root factorization uses nonnegative inputs and the true row variance. The sets are on the finite sample carrier and the probability operations are valid.

`empiricalBernstein_combined_confidence` sets `x=log(5/δ)`, which is positive under its exact `0<δ<1` hypotheses, and verifies `5 exp(−log(5/δ))=δ`. Its conclusion is failure probability `≤δ`, implying success probability **at least** `1−δ`; it does not by itself establish the source's strictly greater success probability. Population variance zero, zero-valued vectors (with a positive supplied B), zero-mass states, and N=1 are not excluded. There is no unrestricted x≤... condition or positive-variance assumption in either final theorem.

## Remaining source gap

The source empirical-Bernstein lemma has a finite random family independent of the empirical row and its outcome-dependent cardinality inside `log(4|𝒱|/δ)`. The staged result only handles one deterministic V and uses `log(5/δ)`, correction coefficient `4√2+2/3` when expanded, and denominator N. It therefore does not prove the source constants `7/3`, `N−1`, or strict simultaneous random-family success. In particular, an unproved union/conditioning argument or simply replacing 5 by 4 cannot close this gap. A suitable source-faithful sharp single-vector theorem and a measurable random-family independence/strict-probability transfer remain necessary.

## Verification and identity

The exact staged source was copied unchanged to a temporary probe, with `#print axioms` for both exports appended, and compiled against integrated `SelfBoundingConcentration` and `SharpEmpiricalBernstein` dependencies using `bash scripts/lean-local.sh`. It exited successfully without diagnostics. Both `empiricalBernstein_combined_exp` and `empiricalBernstein_combined_confidence` depend only on `propext`, `Classical.choice`, and `Quot.sound`. This checks the staged exact source and its imports; integration and production export auditing remain separate. No Lean source was changed by this review.

SHA-256:

- `.local/EmpiricalBernsteinCombined.lean`: `9fe237c05a81a97a745f7cd8d270c0785cd1629f161064722b5d30fc69910ce3`.
- `Formalization/Probability/SelfBoundingConcentration.lean`: `230a7944459f216a7af3b181faeab9c1690a6198496b9bbbf6ae060e52b1845f`.
- `Formalization/Probability/SharpEmpiricalBernstein.lean`: `f47b57d451b8ee49c8b702a834ee99747ec5cca36288bf9344dd08c11a596e67`.
- `Formalization/Probability/EmpiricalVarianceBernstein.lean`: `ac0d89639cdf3396e92dd4c3c7ca5be302952481ca1b8f68751b6dbadd9120c5`.
- `Formalization/Probability/EmpiricalRow.lean`: `6e87c90ff1150f7053845acff92d60a5c35035c7a78adcd394e0da5f3d9dc154`.
- Source `prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
