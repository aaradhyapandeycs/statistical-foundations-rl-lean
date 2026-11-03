# Exponential lower concentration of empirical standard deviation

Builder result, 2026-11-02. Target `.local/SelfBoundingConcentration.lean`, SHA-256 `230a7944459f216a7af3b181faeab9c1690a6198496b9bbbf6ae060e52b1845f`.

**Proved: a genuine exponential empirical-standard-deviation lower tail with the correct N⁻¹ᐟ² scale and weaker constants. Not proved: source sharp empirical Bernstein inequality.** No desired concentration estimate is assumed and no axioms or proof holes were added. This is ordinary staged infrastructure requiring independent review before integration.

## Search and chosen proof route

I searched the pinned Mathlib `Probability` and `MeasureTheory` trees for entropy, tensorization, logarithmic Sobolev, bounded differences, and exponential inequalities. A prior whole-tree search also covered empirical Bernstein, Efron–Stein, McDiarmid and self-bounding terminology. No directly applicable finite-product entropy/tensorization or self-bounding concentration theorem was found. Martingale Borel–Cantelli bounded-difference results concern asymptotic behavior rather than the desired finite-sample tail.

Instead of assuming the missing general theorem, the file obtains a weaker but useful exponential standard-deviation bound directly from the project's proved restricted Bernstein MGF bound and Hoeffding bound. It imports only `Formalization.Probability.EmpiricalVarianceBernstein` and its existing closure; it does not depend on the staged leave-one-out file. The earlier deterministic self-bounding result is still available for a sharper route later.

## Proved mathematical statement

Write μ=PV, σ²=Var_P(V), Z=Var_P̂(V), and m=P̂V, using actual iid samples and the empirical frequency variance with denominator N. For every fixed V∈[0,B], B>0, N>0 and t>0:

`P(√Z+t<σ) ≤ 3 exp(−Nt²/(16B²))`.

A sharper intermediate estimate holds for 0<t≤σ:

`P(√Z+t<σ) ≤ exp(−Nt²/(16B²)) + 2 exp(−Nt²/B²)`.

Consequently for x>0:

`P(√Z+4B√(x/N)<σ) ≤ 3 exp(−x)`.

And for 0<δ<1:

`P(√Z+4B√(log(3/δ)/N)<σ) ≤ δ`.

Thus outside the last strict failure event, population standard deviation is at most empirical standard deviation plus the displayed observable radius. This is a stochastic improvement over the earlier two-moment additive variance bound: it has N⁻¹ᐟ² standard-deviation error rather than the generic N⁻¹ᐟ⁴ error obtained by taking square roots of additive variance error. It does not claim source-optimal constants.

## Proof reconstruction and exported ingredients

Let W(s)=(V(s)−μ)². The file proves:

- `centeredSquare_mem_Icc`: W∈[0,B²].
- `centeredSquare_variance_le`: Var_P(W)≤B²σ², because E[W²]≤B²E[W]=B²σ².
- `empiricalVariance_eq_centeredSquare_sub`: Z=P̂W−(m−μ)², an exact pointwise recentering identity.
- `centeredSquare_lower_tail`: for every explicit u≥0 with uB²≤1, `P(a≤σ²−P̂W)≤exp(−uNa+Nu²B²σ²)`. This applies the already proved restricted Bernstein lower tail to W and proves the variance bound internally. Its only extra inputs are the explicit tuning and range conditions, not any unproved estimate.

For 0<t≤σ, set a=σt/2, r=√a and u=t/(4B²σ). The range condition uB²≤1 is proved from t≤σ. If √Z+t<σ, then σ²−Z>σt, so either σ²−P̂W≥a or |m−μ|≥r. The complement argument preserves the strict/non-strict boundary conventions exactly. The first event has probability at most exp(−Nt²/(16B²)); Hoeffding bounds the second by 2exp(−Nσt/B²)≤2exp(−Nt²/B²). No independence between these two events is assumed or needed. If t>σ, the failure event is empty since √Z≥0. The final confidence conversion uses exact logarithm/exponential identities.

Public tail exports: `empiricalStd_lower_tail_of_le`, `empiricalStd_lower_tail`, `empiricalStd_lower_tail_exp`, and `empiricalStd_lower_tail_confidence`.

## Boundaries and limitations

N=1 is included and the bound may be uninformative; N=0 is excluded. A zero population variance causes no division problem in the final theorem because t≤σ is then impossible; the proof takes the empty-event branch. Constant vectors, endpoint values 0/B and deterministic laws are included. A zero vector can be supplied any positive B, but the formal B=0 case is excluded by the final range assumption; a separate zero-range declaration was not added. All tail thresholds t and x are strictly positive. Probabilities are genuine real measures under the finite iid product `sampleMeasure N`; no external concentration hypothesis is attached to that measure.

Source: arXiv:2610.41903v1, `source/upstream/tex/chapters/prelim.tex:983–998`, label `empirical bernstein`. Its exact mean-error radius is

`√(2 log(4|𝒱|/δ)/(N−1)) √Var_P̂(V) + 7 ‖V‖∞ log(4|𝒱|/δ)/(3(N−1))`.

The new standard-deviation confidence radius has constant 4 and log(3/δ), and establishes no mean-error event, source 7/3 coefficient, N−1 source scaling, strict source success probability, or simultaneous independent random-family lifting. Combining it with the existing weaker population-variance Bernstein tail could yield a weaker self-normalized mean bound, but that assembly is not claimed here. A sharper finite-product self-bounding/entropy concentration proof or equivalent direct argument is still missing for the source constants. The deterministic leave-one-out quadratic bound alone does not supply that theorem.

## Validation

Pinned Lean `v4.27.0-rc1`, Mathlib `32d24245c7a12ded17325299fd41d412022cd3fe`. Compiler slots coordinated with the lead and other worker; dependency artifacts preserved.

- `bash scripts/lean-local.sh .local/SelfBoundingConcentration.lean`: exit 0, no diagnostics for the general tail and exponential radius.
- Final exact-source copy `<temporary-probe>/SelfBoundingConcentrationAxioms.lean`, including the δ-confidence theorem and eight `#print axioms` checks: `bash scripts/lean-local.sh <temporary-probe>/SelfBoundingConcentrationAxioms.lean` — exit 0, no diagnostics.
- All eight public declarations have transitive axiom closure exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, custom axiom or admitted dependency. Temporary probe deleted.

Only the assigned staged Lean file and this builder note were written. No source closure or independent certification is claimed. The lead must arrange independent semantic review and actual export integration checks.
