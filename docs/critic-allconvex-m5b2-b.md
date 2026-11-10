# CRITIC m5b2-B: pass-2 reservoir Lindeberg (T^-1/3), AC lemma / arithmetic / TD application

Public copy, scrubbed (local paths, probe files and agent identifiers removed). One of two independent infrastructure reviews (this one: the anti-concentration lemma, the final arithmetic and the TD application) of the convex Berry–Esseen bound at `n^{-1/3}` for the reservoir Lindeberg swap and its TD application (`Formalization/Probability/GaussianMixedThird.lean`, `Formalization/Probability/ConvexLindebergReservoirSharp.lean`, `Formalization/Ch7Rest/TDInferenceConvexLinSharp711.lean`). Not a source result: it covers only the linear part of the TD statistic; no statement-index entry. Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT; cosmetic fixes applied at integration (module docstring regimes use `⌈n^{2/3}⌉` and `max r₀ 1`; anti-concentration docstring says the reservoir is scaled by `3^{-1/2}`; unused `have` removed).

Reviewer: independent critic B (not the builder). Date 2026-11-10. No edits to Formalization/, docs/, Formalization.lean.

## Verdict: ACCEPT (as infrastructure; not Theorem 7.11)

## Evidence (commands actually run)
- `bash scripts/lean-local.sh Formalization/Probability/ConvexLindebergReservoirSharp.lean`: clean, no errors or warnings (20.9 s).
- `bash scripts/lean-local.sh Formalization/Ch7Rest/TDInferenceConvexLinSharp711.lean`: clean (2.4 s).
- <local probe>: `#print axioms` of abs_linLaw_convex_sub_gaussCov_le_third, ..._of_burnIn, abs_pexp_convex_sub_twinLaw_le_third, pexp_shell_prefix_le, reservoirCond_acL, twelfth_facts, sum_range_le_three: all exactly [propext, Classical.choice, Quot.sound]. `reservoirThirdConst ι c r₀ B` unfolds by rfl to shellConst + thirdSmoothConst + sharpBurnIn^{1/3} (no n). `splitScale^2 c/2 = c/6` checked.
- <local probe> (copy of builder probe): rad_convex_le_third (generic, every n >= 1) and g_linConvex_third (instance G, Gamma_true = (25/128, 1/128) > 0) compile, axiom-clean. Hypotheses are satisfiable; conclusion K T^{-1/3} -> 0 is non-trivial.
- grep: no sorry/admit/axiom/set_option in the two targets or GaussianMixedThird.lean.

## (1) Anti-concentration `pexp_shell_prefix_le` (Sharp.lean:846-989)
Verified by hand and against the code:
- Modified family acY/acL (:636-645): index with e.symm i = k zeroed, indices < k unchanged, indices > k scaled by a = 3^{-1/2}. prefixSum_acY (:646) shows the modified prefix at k+1 equals the original prefix at k; twinMat_acL_resSet (:658) gives a * twinMat L (resSet k); with gaussSet(k+1) = resSet k this identifies the modified hybrid H'_{k+1} with prefix_k + a*R*Z (hhyb, :920). Correct.
- reservoirCond_acL (:715): for r >= max r0 ceil(2 S B^2/c), sum over last r of modified quadratic forms >= a^2 (c r/n)|u|^2 - a^2 q_k with q_k <= S B^2 |u|^2 / n (quadForm_le_of_cov, :587, Cauchy-Schwarz with sup-norm bound; correct), and S B^2 <= c r/2 gives >= (a^2 c/2) r/n |u|^2 = (c/6) r/n |u|^2. Indices < k use a^2 q <= q (a^2 <= 1). Correct; no hidden hypothesis.
- Mean/cov/bound transfer (acY_mean/acY_cov/acY_bound) correct; bound stays B/sqrt n.
- Pass-1 partial telescoping at k' = k+1 <= n with smoothing scale n^{-1/4}; sandwich of the translated shell indicator by gu - gl; Gaussian side via thickening/M2 split into shellSet(eps0+delta) and twinLaw shell bound (needs r0' <= n, supplied by hN). Result Csh(c/6)(delta + n^{-1/4}) + 2 Q0/n^{1/4}, constants depend only on |iota|, c, r0, B. Matches the claim.

## (2) Arithmetic (Sharp.lean:993-1104, 1157-1350)
- harmonic sum <= 1 + log n via Mathlib harmonic_le_one_add_log; log n <= 12 n^{1/12} via Real.log_le_rpow_div with eps = 1/12; s = n^{-1/12} identities in twelfth_facts all correct.
- Mixed per-step Ab/j with Ab <= mixedConst * s^5 (mixed_arith: s^8 <= s^5, s, s^3 <= 1); Ab(1+log n) <= 13 mixedConst s^4 = 13 mixedConst n^{-1/3}. Correct.
- Unsmoothed regime J0 = max r0 1 steps each O(n^{-1/2}) <= s^4; reservoir regime 4 Aa / sqrt(max J0 J1) with J1 = ceil(n^{2/3}) gives <= 4 Aa n^{-1/3}. Correct.
- Small n (< sharpBurnIn): trivial bound 1 <= sharpBurnIn^{1/3} n^{-1/3} (:1359). Correct, constant n-free.

## (3) TD application (TDInferenceConvexLinSharp711.lean)
- Instantiation (:65-71): p = tupleProb, Y = linSummand, L = linFactor, c = min Gamma_true/(32 S), r0 = 1, B = linWeightConst * tdNoiseBound, ReservoirCond from exists_linFactor_reservoirCond_of_pos (needs T >= linReservoirBurnIn) - same as pass 1.
- Gaussian-vs-Gaussian (:83-111): abs_real_convex_gaussian_sub_le with v = min(c, v2) and entryMax_linCov_sub_le, which is already linCovConst * T^{-1/3`. Correct rate.
- Wrapper (:132-162): K = |K1| + linReservoirBurnIn^{1/3} + 1 > 0, chosen before T and C; small T handled by the <= 1 bound. Hypotheses identical to the _quarter export. No hidden hypotheses.

## Findings
1. (Info) TDInferenceConvexLinSharp711.lean:132-135 allows 0 < eta0 <= 1 while thm:Berry-Esseen-linear (inference.tex:132-141) assumes 0 < eta0 < 1/4: the export is more general, not a discrepancy.
2. (Info, honesty OK) Module header (:4-20) and docstrings (:122-131, Sharp.lean:1361-1366) explicitly say partial, linear part only, Gamma_true correction C43, instance constant, not Theorem 7.11, no statement-index entry. No overclaim found. Rate matches the printed T^{-1/3}; the printed coefficient is not obtained (disclosed).
3. (Low, integration) Both files are not imported from Formalization.lean, so the public axiom audit does not yet cover them; the lead must add imports on landing (and keep no Statements entry, since no source result is proved).
4. (Low, doc nit) Sharp.lean:841-845 docstring says "a third of the reservoir"; precisely it is the reservoir factor scaled by 3^{-1/2} (covariance one third). Accurate in substance.

No REJECT- or FIX-level issues in my focus areas.
