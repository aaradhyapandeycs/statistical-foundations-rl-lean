# Critic A review: m5b2 pass-2 reservoir Lindeberg (n^{-1/3})

Public copy, scrubbed (local paths, probe files and agent identifiers removed). One of two independent infrastructure reviews (this one: the shell-supported smoothing inequality, the three-regime split and the mixed bound) of the convex Berry–Esseen bound at `n^{-1/3}` for the reservoir Lindeberg swap and its TD application (`Formalization/Probability/GaussianMixedThird.lean`, `Formalization/Probability/ConvexLindebergReservoirSharp.lean`, `Formalization/Ch7Rest/TDInferenceConvexLinSharp711.lean`). Not a source result: it covers only the linear part of the TD statistic; no statement-index entry. Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT; cosmetic fixes applied at integration (module docstring regimes use `⌈n^{2/3}⌉` and `max r₀ 1`; anti-concentration docstring says the reservoir is scaled by `3^{-1/2}`; unused `have` removed).

Critic: independent reviewer A (not the builder). Date 2026-11-10.
Targets: Formalization/Probability/GaussianMixedThird.lean (559 lines),
Formalization/Probability/ConvexLindebergReservoirSharp.lean (1415 lines).
Focus: smoothing-with-shell-support, the three step regimes, and the mixed step.
Out of scope (critic B): pexp_shell_prefix_le / reservoirCond_acL, final harmonic arithmetic, TD application.

## Commands and evidence
- `bash scripts/lean-local.sh Formalization/Probability/GaussianMixedThird.lean`: exit 0, no output (5.6 s).
- `bash scripts/lean-local.sh Formalization/Probability/ConvexLindebergReservoirSharp.lean`: exit 0, no output (21 s).
- Oleans are newer than the sources (Sharp src 01:13:37, olean 01:14; Mixed src 20:51, olean 20:54).
- Probe <local probe>: `#print axioms` on
  abs_pexp_convex_sub_twinLaw_le_third, abs_pexp_sub_twinLaw_le_smooth_third,
  abs_hexp_succ_sub_le_mixed, abs_pexp_indicator_sub_le_of_smooth_supp, pexp_abs_taylorRem_le,
  sum_range_le_three: all `[propext, Classical.choice, Quot.sound]`. An independently typed
  restatement of the main export (explicit binders, my own spelling) is closed by the export.
- grep: no sorry/admit/axiom/native_decide/implemented_by in either file.

## Verdict: ACCEPT (with optional cosmetic fixes)

## Checks performed
(1) Shell-supported smoothing. `abs_pexp_indicator_sub_le_of_smooth_supp` (GaussianMixedThird.lean:430)
quantifies the smooth hypothesis only over tests whose fderiv vanishes off `shellSet ε K`
(= cthickening ε K ∩ cthickening ε (interior K)ᶜ, identical to the set bounded by
`twinLaw_convexShell_le`). The upper/lower sandwiches satisfy this by `fderiv_eq_zero_of_upper/lower`
(:396, :414): off cthickening ε K the upper sandwich is locally 0 (closure of thickening ⊆ cthickening),
off cthickening ε (interior K)ᶜ the point is in interior K so it is locally 1; the lower sandwich is
locally 0 off closure K and locally 1 on the open complement of cthickening ε (interior K)ᶜ. No convexity
or measurability of K used; correct. The main theorem instantiates ε = n^{-1/3} consistently in hd,
hsupp and the shell bound (Sharp:1389-1395).

(2) Regimes. `sum_range_le_three` (Sharp:1009) splits on j = n-1-k: j < J₀; J₀ ≤ j < J₁; J₀ ≤ j ∧ J₁ ≤ j.
Disjoint and exhaustive (by_cases chain, :1033-1050); each step charged once. J₀ = max r₀ 1 (so both
smoothed regimes have r₀ ≤ j and j ≥ 1, needed by reservoir_quadForm), J₁ = ⌈n^{2/3}⌉ = ⌈(s⁸)⁻¹⌉.
Unsmoothed cost Ac = O(n^{-1/2}) times J₀; reservoir tail 4Aa/√max(J₀,J₁) ≤ 4Aa n^{-1/3}.

(3) Mixed step. `gaussSmooth_eq_three` splits R into three copies of 3^{-1/2}R (semigroup with
1/3 + 2/3 and 1/2 + 1/2). `dirDeriv_three_eq` puts one derivative on φ (innermost smoothing retained)
and Gaussian weights ⟨v,w⟩, ⟨v,w'⟩ on the outer two (two applications of
`dirDeriv_gaussSmooth_eq_integral`, S₀v = h). Segment-local Taylor: `abs_taylorRem_le_of_dirDeriv`
needs |D_h³F| ≤ M only on [U, U+h]; the majorant χ is the upper sandwich of the (‖h‖+ε)-shell, so
|D_hφ(y+th)| ≤ D‖h‖χ(y) for t ∈ [0,1] (mem_shellSet_of_add_smul), and χ ≤ 1_{shell(2ε+‖h‖)}
(thickening_shellSet_subset). Second-moment cancellation `sum_sub_integral_eq_taylorRem` is exact
(linear term zero by mean, quadratic term equal by covariance; integrability of the Gaussian side
proved). Gaussian side carries ‖Lz‖ in the shell width, giving the ‖Lz‖⁴ term bounded by
matrixAbsSum⁴·E‖Z‖⁴ (`integral_norm_mulVec_pow_four_le`, finite via coordinatewise 4th moments).
∑v² ≤ 3S²/v₀·‖h‖² with v₀ = cj/n. Per-step cost: D·(3S²n/(cj))·(σ₀+Csh(2ε+b))·A₃b³ with
D = c₁n^{1/3}, b = Bn^{-1/2}, σ₀ = O(n^{-1/4}) gives O(n^{-5/12}/j); the fourth-moment part is
O(n^{-2/3}/j). `mixed_arith` (Sharp:1157) proves Ab ≤ mixedConst·s⁵ with s = n^{-1/12}, i.e. the
claimed n^{-5/12}/j is exactly what is proved; the equality step at Sharp:1290 confirms the step
bound equals Ab/j.

Constants: `#print reservoirThirdConst` unfolds to shellConst ι c + thirdSmoothConst ι c r₀ B +
sharpBurnIn^{1/3}; all components depend only on |ι|, c, r₀, B (no n, K, p, L). The small-n branch
(n < sharpBurnIn) is the trivial bound 1 ≤ sharpBurnIn^{1/3} n^{-1/3}; legitimate.
Non-vacuity: builder's Rademacher witness `rad_convex_le_third` (m5b2-wip/Probe.lean) uses
ReservoirCond with r₀ = 0, c = 1; I did not find any hidden hypothesis.

## Findings
1. (Info) Sharp:1371 / docstring "measurable or not": for non-measurable convex K,
   `(twinLaw L).real K` is the outer measure. Statement is still true and meaningful (and stronger
   than Borel-only), but any downstream prose should say "outer measure" or restrict to measurable K.
2. (Cosmetic) Sharp:1226 `have hr₀n` is unused in `abs_pexp_sub_twinLaw_le_smooth_third`.
3. (Cosmetic) Sharp module docstring (:24-31) states the regimes as j ≥ n^{2/3} / j < n^{2/3}; the
   code uses J₁ = ⌈n^{2/3}⌉ and the top regime also requires j ≥ max r₀ 1. Harmless, but could be
   stated exactly.
4. (Info) Regime-b sum uses 1 + log n over all j rather than j < J₁; loose but correct.
No blocking or source-fidelity findings in my scope. (This is infrastructure, no statement-index
entry, consistent with AGENTS.md.)
