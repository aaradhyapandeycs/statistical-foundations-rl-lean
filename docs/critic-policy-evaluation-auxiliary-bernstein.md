# Independent review: simultaneous auxiliary-value Bernstein event

**Verdict: PASS for the displayed simultaneous event under the actual fixed-policy sampling law.** The staged theorem controls all states and every auxiliary level 0 through m inclusive, has the correct explicit `m+1` count, and derives strict success probability without assuming a concentration event or independence between levels. The comparison with the source's informal `C₀ log(Sm/δ)` requires the domain distinction below. This is a scoped staged result, not a proof of the source's full sharp policy-evaluation theorem or an author-approved frozen declaration.

Reviewed `.local/PolicyEvaluationAuxiliaryBernstein.lean`, SHA-256 `2a4a6df841a284b0db5a1b157d2240ee43e60ed060bd3b81bb47b03c95da3671`; its exact staged `.local/PolicyEvaluationAuxiliary.lean` dependency, SHA-256 `68a6bc19097ecc84a93583a39230b92b58b4a3ab8a2c0971ab50d084923bbb95`; and `docs/builder-policy-evaluation-auxiliary-bernstein.md`. The authoritative source is `source/upstream/tex/chapters/generative_model_model_based.tex:413–480`, in particular `eq:Bernstein-Vl` at 471–480; source SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`. The source fixed-policy iid sampling experiment is lines 78–100, and the source row Bernstein inequality is `prelim.tex:956–965`.

## Sampling, vectors, and quantifiers

For any valid finite MDP M and any fixed stationary randomized π, `samplingLaw M π N` is the genuine product of actual policy-row transition laws over every `(s,i)` with i among N sample indices. The integrated `samplingLaw_stateRow` proves each entire row-sample sequence has the true N-fold iid product law. `empiricalPolicyRow` is its actual normalized sample-frequency distribution, and `M.policyTransition π s` is the true stochastic policy row. The empirical-minus-true expectation in the event is therefore exactly `[(P̂_π−P_π)V^l](s)`.

Each `auxiliaryValue M π l` is defined from the **fixed true MDP and policy**, its actual infinite-trajectory value, true transition variance and true resolvent. It does not take the sampled data. Thus each vector is deterministic with respect to the sample law, and the proof applies a deterministic fixed-vector Bernstein estimate directly to its actual row law. It need not separately assume independence of vectors or of their levels; in fact the vectors may coincide and repeated copies do not invalidate the union bound. π is fixed before data collection; no data-selected policy claim is made.

The theorem quantifies over every state and `l : Fin (m+1)`, exactly the inclusive natural levels `0,…,m`. It handles m=0, where the one level is l=0. M supplies a nonempty finite state carrier, N>0 is required for empirical frequencies, and 0<δ<1 matches the source. `auxiliaryValue_nonneg` proves every vector is coordinatewise nonnegative, including zero vectors and γ=0; no positive norm, positive variance, sample-size lower threshold, or desired event is a final theorem hypothesis.

## Exact radius and strict probability

Put `S=card State`, `K=m+1`, `η=δ/S`, and `L=log(4SK/δ)`. Each `(s,l)` strict violation of `bernsteinRadius` has probability at most `η/(2K)=δ/(2SK)` by the source's fixed-vector Bernstein bound. Pullback uses the proven actual row-law marginal. The union over precisely `S·K` pairs has probability at most δ/2. Its complement lies in the displayed simultaneous event, whose probability is consequently at least `1−δ/2>1−δ`; no independence between bad events is used. Finite sample spaces make the relevant sets measurable.

`auxiliaryValues_bernstein_explicit` proves the literal radius

```text
sqrt(2 L/N) sqrt(Var_{P_π(s)}(V^l))
  + 2 ‖V^l‖∞ L/(3N),     L=log(4S(m+1)/δ).
```

The inequality for each deviation is non-strict, and the probability statement is **strict** `>1−δ`. The true population variance, finite sup norm, factor 4, 2 and 3, and actual random sample law all match the fixed-row Bernstein infrastructure. Selecting `β₁=2L` gives the source-shaped square-root term exactly and dominates the source-shaped linear term because `2L/(3N)≤2L/N` for positive L. The source's `β₁=C₀ log(Sm/δ)` requires the following separate numerical comparison; the staged theorem itself retains the literal correct logarithm and does not assert that comparison.

## Inclusive-count logarithm: precise source domain

For arbitrary m≥1, it is **not** enough by itself to say `2log(4S(m+1)/δ)≤C₀ log(Sm/δ)` for one universal C₀: with `S=m=1` and δ approaching 1, the right-hand logarithm tends to 0 while the left tends to `2log 8`. At m=0 the source expression `log(Sm/δ)` is undefined, whereas the staged event remains meaningful. This is an algebraic correspondence caveat, not a counterexample to the Bernstein event or the source theorem.

For the source's intended positive-discount specialization, however, `m=ceil(log(e/(1−γ)))` and `0<γ<1` imply `m≥2`: `log(e/(1−γ))>1`. With S≥1 and δ<1, `x=Sm/δ>2`; also `4S(m+1)/δ≤8x≤x⁴`. Hence

```text
β₁ = 2log(4S(m+1)/δ) ≤ 8log(Sm/δ).
```

A universal source constant C₀ at least 8 therefore suffices for this comparison on that precise domain. This paragraph is a mathematical source check, not a Lean lemma exported by this file. At γ=0, the source's chosen m can equal 1 and its other recursion constants contain `1/γ`; a separate exact zero-discount argument is needed rather than silently using the positive-γ comparison. A different explicit convention such as `log(8Sm/δ)` could also avoid the vanishing-log issue, but would be a source-facing change requiring a visible ruling.

## Independent verification and remaining work

The exact staged auxiliary dependency was rebuilt to its local `.olean`, then an unchanged copy of `.local/PolicyEvaluationAuxiliaryBernstein.lean` with both `#print axioms` commands appended was compiled using the local dependency and the existing project/package build paths. Both `auxiliaryValues_bernstein` and `auxiliaryValues_bernstein_explicit` compile without diagnostics and use only `propext`, `Classical.choice`, and `Quot.sound`. The dependency source was separately independently reviewed in `docs/critic-policy-evaluation-auxiliary.md`. This is staged verification; changing imports for integration requires a separate exact-export check. No Lean source was modified in this review.

The event does not prove the sharper source growth estimate for all auxiliary levels, positivity/entrywise comparison of the empirical resolvent, the recursive error inequalities, terminal remainder, or final horizon-three sample theorem. Those pieces and the source-domain logarithm comparison require separate formal proofs and review before a full theorem claim.

## Integrated export recheck

`Formalization/Generative/PolicyEvaluationAuxiliaryBernstein.lean` has SHA-256 `9e2e36577d44de8e1cab50a519f92ed093074cbeea62009565e55d41d190486d`; a direct diff against reviewed staged SHA `2a4a6df841a284b0db5a1b157d2240ee43e60ed060bd3b81bb47b03c95da3671` shows only the first import changed from the staged `PolicyEvaluationAuxiliary` to `Formalization.Generative.PolicyEvaluationAuxiliary`. The actual integrated dependency and event modules were built sequentially to their previously absent project-owned `.olean` files with `bash scripts/lean-local.sh`. An independent import-only probe confirmed `auxiliaryValues_bernstein` and `auxiliaryValues_bernstein_explicit` again use only `propext`, `Classical.choice`, and `Quot.sound`. Both builds and the probe passed without diagnostics. This does not remove the source-domain and remaining-proof limitations above.
