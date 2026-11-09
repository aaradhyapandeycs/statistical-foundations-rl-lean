# CRITIC: item B (oracle-covariance confidence intervals) and E2 (C47(1) evidence)

Public copy of the independent critic report; local paths removed. Probe and scratch files named below (`reviewer-probes/`, `builder-probes/`) were kept in private folders and are not published.

Post-review note (added to this public copy, 2026-11-09): the entry was integrated under the recommended name `Eq_convex_Cdelta_corrected_oracle` (R2) with the recommended docstring (R1) and the `open ... in` line of R4, in `Formalization/Statements/Ch7.lean`, with the wrapper in `Ch7Proofs.lean`. R3, F3 and F4 were applied to the module and theorem docstrings, F2 was added as `convex_signSel`, and F1 corrected the C47 locators. The COVERAGE row uses the "Partial" headline. The review text below is otherwise unchanged.

Critic: independent (not the builder). Date: 2026-11-09.
Under review: `Formalization/Ch7Rest/TDInferenceConfInt711.lean`, `Formalization/Ch7Rest/TDInferenceC47Evidence711.lean`,
`builder-probes/{DRAFT-STATEMENT.lean, ProbeG.lean, STATUS.md}`.
Source: `source/upstream/tex/chapters/inference.tex`, SHA-256
`82707713adb6c9296d9ee41faa84b2d0a12eaf1b34864a6d294de02132e648f2` (matches the C47 pin).
Brief: the private Chapter 7 inference plan item B / E2 as amended by the plan check (`docs/critic-ch7-inference-plan-check.md`) (4), (6).

## Verdict: ACCEPT WITH FIXES

The mathematics and the Lean are correct. B1, B2, B3 and E2 are proved as stated, with no hidden hypotheses and a
clean axiom closure. The fixes concern docstrings (one wrong-object claim in E2, one misattribution in the entry)
and the entry name. No library theorem signature needs to change.

## Evidence (commands actually run, one Lean process at a time, `pgrep -x lean | wc -l` checked < 2 before each)

- `bash scripts/lean-local.sh Formalization/Ch7Rest/TDInferenceConfInt711.lean`: no output (clean), 5.4 s.
- `bash scripts/lean-local.sh Formalization/Ch7Rest/TDInferenceC47Evidence711.lean`: clean, 2.8 s.
- Sanity: a deliberately false `rfl` in `reviewer-probes/Sanity.lean` is reported as an error, so the runner really elaborates.
- `reviewer-probes/ProbeEntryCtx.lean`: imports only `Formalization.Statements.Ch7`, puts the draft `def` in
  `namespace StatisticalRL.Statements.Ch7`: compiles. So the G2 import gate holds (no new `Formalization.*` import;
  `gaussianReal`, `tdA`, `trueGamma`, `prAverage`, `pathWeight` come through `TDInference711Defs`). It needs
  `open MeasureTheory ProbabilityTheory Matrix` (for `gaussianReal`, `diagonal`, the `ᵀ` notation) in addition to
  `open StatisticalRL StatisticalRL.Ch7Rest.TDInference`.
- `reviewer-probes/ProbeFull.lean`: `import Formalization` + `TDInferenceC47Evidence711`; draft `def` + `_holds` wrapper
  inside `StatisticalRL.Statements.Ch7`, plus critic checks (a)–(e). Clean (no error, warning or sorry), 62 s. No name
  collision with the full library (the import of both would fail otherwise; the entry name is fresh in the namespace).
  `#print axioms` of `Eq_convex_Cdelta_restricted_oracle_holds`, `exists_coverage_oracle_bounds`,
  `abs_coverage_oneSided_sub_le`, `abs_coverage_twoSided_sub_le`, `coverage_rect_bonferroni_ge`,
  `oneState_signSel_coverage`, `oneState_signSel_coverage_eventually_lt`, `gaussianReal_signSel`,
  `oneState_oracleLambda`: all `[propext, Classical.choice, Quot.sound]`.
- `reviewer-probes/ProbeG_copy.lean` (verbatim copy of the builder's ProbeG): clean. Non-vacuity on G (two states,
  Γ_true = (25/128, 1/128) ≻ 0, η₀ = 1/8) confirmed, including a concrete `u = e_0, z = 0` consequence.
- `grep sorry|admit|axiom` on both library files: no hits. Text grep of all 25 new declaration names over
  `Formalization/**/*.lean`: no other definitions (`OneState` occurs only as a `section`/module name elsewhere).

## Reconstruction

**(1) Pivot / half-space translations.** For T ≥ 1, `√T > 0` and `√(r/T) = √r/√T`, so
`uᵀV̄ − z√(r/T) ≤ uᵀV^π ⇔ √T(uᵀV̄ − uᵀV^π) ≤ z√r` and `|d| ≤ z√(r/T) ⇔ |√T d| ≤ z√r` (`sub_mul_sqrt_div_le_iff`,
`abs_le_mul_sqrt_div_iff`; the second holds for any sign of z because both sides scale by √T > 0).
`uᵀ scaledError = √T(uᵀV̄ − uᵀV^π)` is exact (`sum_mul_scaledError`). The coverage sums are therefore literally
`lawProb` of the closed half-space `{uᵀx ≤ z√q}`, the slab `{|uᵀx| ≤ z√q}` and the box `{∀s, |x_s| ≤ z√Λ_ss}`.
Signs: B1's event is `uᵀV^π ∈ [uᵀV̄_T − z√(q/T), ∞)` (a lower confidence bound), and its probability is
`P(uᵀ√TΔ̄_T ≤ z√q) → Φ(z)`. Correct. q = uᵀΛu > 0 for u ≠ 0 is proved from `mul_sq_sum_abs_le_quadForm` with
g = min Γ_true > 0 and A invertible (`quadForm_oracle_pos`). Gaussian side: `N(0,Λ)(uᵀx ≤ z√q) = Φ(z√q/√q) = Φ(z)`.
Correct for every z ∈ ℝ.

**(2) B2, B3, Φ.** Pointwise `1{|w| ≤ c} = 1{w ≤ c} + 1{−w ≤ c} − 1` for c ≥ 0 (the case w > c ∧ −w > c is
impossible since c ≥ 0); summing against path weights that total 1 gives `P(slab) = P(H(u)) + P(H(−u)) − 1`; the
quadratic form of −u equals that of u, so each half-space term is within K T^{-1/3} of Φ(z) and the slab is within
2K T^{-1/3} of 2Φ(z) − 1. Correct; z ≥ 0 is needed (c = z√q ≥ 0) and is assumed. B3: each coordinate slab
(u = e_s, quadratic form Λ_ss) fails with probability ≤ 2(1 − Φ(z)) + 2K T^{-1/3}; the pointwise union bound
`1 − Σ_s(1 − 1_{C_s}) ≤ 1_{∩C_s}` summed against nonnegative weights totalling 1 gives
`≥ 1 − 2S(1 − Φ(z)) − 2SK T^{-1/3}`. Correct; one K throughout, uniform in u, z, T.
`Φ(z) = (gaussianReal 0 1).real (Set.Iic z)` is the standard normal CDF. Correct.

**(3) E2.** Instance O: `State = Unit`, actions {0,1}, `r(·,a) = (0,1)` (action dependent; checked
`oMDP.reward () 0 = 0`, `oMDP.reward () 1 = 1`), γ = 1/2, π and μ uniform. `tupleProb = μ(s)·π(a|s)·P(s'|s,a)`, so
the sampled action, hence the reward, is random: this is genuinely the book's TD model with noise from the
action-reward variance. Hand check: V^π = (1/2)/(1 − 1/2) = 1; TD residual r + γ·1 − 1 = ±1/2, so Γ_true = 1/4;
A = 1·(1 − 1/2) = 1/2; Λ = 2·(1/4)·2 = 1. All four are Lean lemmas.
`signSel ρ v = [v − ρ, ∞) if v ≥ 1 else (−∞, v + ρ]` has type `ℝ → ℝ → Set ℝ`: it uses only the data (and the fixed
number 1), not M, π, μ. **But the threshold 1 equals V^π of O, and that is essential**: for a fixed threshold c ≠ V^π,
V̄_T eventually lies on one side w.h.p. and the coverage tends to Φ(z), not 2Φ(z) − 1. The counterexample is
"∃ instance, ∃ data-measurable convex-set-valued rule with conditional mass exactly 1 − α that under-covers", with
the rule tuned to the instance. This is the right quantifier order to refute the printed text, which is universal
over sets ("it suffices to choose any convex set C_α ..." :189, "such sets serve as approximate confidence regions"
:196), and it is exactly the structure of the paper witness in C47(1) (threshold 0 = θ). So E2 does demonstrate
C47(1)'s point, for the oracle-covariance variant, provided the docstring says the threshold coincides with V^π
(R3 below). Undercoverage: |cov − (2Φ − 1)| ≤ 2K T^{-1/3} (B2 with u = 1, S = 1, Λ = 1); once
2K T^{-1/3} ≤ (1 − Φ)/2, cov ≤ 2Φ − 1 + (1 − Φ)/2 = Φ − (1 − Φ)/2, and 1 − Φ(z) > 0 (`stdTail_pos`). Correct.
The critic probe derives the strict `cov < Φ(1)` eventually from the export (check (c)). The selected sets have
mass exactly Φ(z) under `N(v, 1/T)` for every v (`gaussianReal_signSel`), i.e. the **oracle** Gaussian
N(V̄_T, Λ/T), not the printed N(V̄_T, Λ̂_T/T).

**(4) Entry honesty and name.** The `Prop` is self-contained, all quantifiers explicit, and equal (up to η₀ < 1/4
⇒ η₀ ≤ 1) to the combined export; the wrapper only applies the export. Problems are in the docstring and name:

- The docstring says "covariance corrected to Γ_true (C43)". That misattributes. The rule `eq:convex.Cdelta` uses
  Λ̂_T (`:180–182`), whose Γ̂_T (`:166–169`) already targets the per-sample residual covariance (C43 says this). The
  C43 correction concerns Λ* (`eq:defn-Lambdastar`, :106–117) in Theorem 7.11, which the claim at :196 invokes. The
  oracle Λ = A⁻¹Γ_trueA⁻ᵀ is the population counterpart of the printed Λ̂_T; its consistency (item C) is not proved.
- Name. The proved statement is not a special case of the printed one: the printed claim concerns sets built
  from Λ̂_T and arbitrary data-selected convex sets, and C47(1) (now with Lean evidence, E2) says that claim is
  false as printed. The C47 proposed correction is precisely "prescribe a rule whose shape given the pivot is
  fixed". The entry is that **correction**, further **restricted** to the oracle covariance and to half-lines, slabs
  and a Bonferroni box. `_restricted_oracle` makes `classify` (gen_nodes) badge it `restricted`, which reads as "a
  special case of a correct printed claim". `_corrected_oracle` (badge `corrected`, with a disclosed restriction) is
  more accurate, and matches the CHECK's naming of item D (`Eq_convex_Cdelta_corrected`). Both suffixes are
  permitted by AGENTS, but per the AGENTS rule "it assumes more, concludes less, or concerns a different object", this
  one concerns a different object, so `_corrected` fits.
- Line locators: rule `:189–195` (display :191–193, label :192, "with V ∼ N(V̄_T, Λ̂_T/T)" :195), claim `:196`,
  rectangles `:198–205`, ellipsoids `:207–213`. The draft's "claim :194–196" should be `:196`.
- "Partial" COVERAGE headline: required and correct (gen_nodes `partial_lead` and the fail-closed rule).

**(5) Hidden hypotheses / non-vacuity.** Hypotheses: full-support μ, 0 < η₀ < 1/4, Γ_true ≻ 0 (disclosed; the printed
Theorem 7.11 uses ‖Γ⁻¹‖ and κ(Γ)), T ≥ 1, u ≠ 0, z ≥ 0 for two-sided and box. None hidden. Satisfiable on O
(η₀ = 1/8, μ = 1, Γ_true = 1/4) and on G (two states). Note: the existential K makes the content asymptotic (rate
T^{-1/3}); for small T the bounds may be trivial, as for the base theorem. This is inherent and already disclosed in
`Thm7_11_corrected_halfspace`.

## Required fixes

- **R1 (entry docstring).** Replace "covariance corrected to `Γ_true` (`docs/SOURCE-ISSUES.md#C43`)" by the text in
  the recommended docstring below (oracle = population target of Λ̂_T; C43 concerns Λ* used in the :196 justification).
  Fix the claim locator to `:196` and the rule locator to `:189–195`.
- **R2 (entry name).** Rename to `Eq_convex_Cdelta_corrected_oracle` (classify → `corrected`). If the lead keeps
  `_restricted_oracle`, the docstring must still say the printed general claim is refuted (C47(1)) and that the entry
  is the C47 fixed-shape correction with an oracle restriction, not a special case of the printed claim.
- **R3 (E2 docstring, wrong object).** In `TDInferenceC47Evidence711.lean` header: "i.e. it is a `(1−α)`-region of the
  printed rule's Gaussian" is false: the printed Gaussian is N(V̄_T, Λ̂_T/T). Say "of the oracle Gaussian
  N(V̄_T, Λ/T)". Also replace "The threshold `1` is a fixed number (the rule is a fixed function of the data, not a use
  of `V^π`)" by: "The rule reads only the data, but its threshold `1` is chosen equal to `V^π` of instance O; this is
  essential (for a threshold `c ≠ V^π` the coverage tends to `Φ(z)`) and legitimate, since the printed claim is
  universal over convex sets with conditional mass `1 − α`: one instance and one data-measurable rule refute it. Same
  structure as the Gaussian witness of C47(1) (threshold `0 = θ`)." And "eventually below" → "eventually at most";
  state `z ≥ 0` (`α = 1 − Φ(z) ∈ (0, 1/2]`).
- **R4 (Ch7.lean placement).** The entry needs `open StatisticalRL StatisticalRL.Ch7Rest.TDInference MeasureTheory
  ProbabilityTheory Matrix in` (verified in `reviewer-probes/ProbeEntryCtx.lean`; `ᵀ`, `diagonal`, `gaussianReal`).

## Optional fixes

- **F1.** C47 locators drift by about 2 lines against the pinned file: rule cited `:185–194`/`:186–194` → `:187–196`
  (paragraph :187, display :191–193, claim :196); rectangles `:196–203` → `:198–205`; ellipsoids `:205–213` →
  `:207–213`; plug-in `:160–181` → `:156–185`; `eq:defn-hat-Lambda` `:179–181` → `:180–182`.
- **F2.** Add `theorem convex_signSel (ρ v : ℝ) : Convex ℝ (signSel ρ v)` (two cases, `convex_Ici`/`convex_Iic`) so
  that "convex" in E2 is machine-checked rather than evident.
- **F3.** `TDInferenceConfInt711.lean` header line "SOURCE-ISSUES C43 (covariance `Γ → Γ_true`)" has the same
  misattribution as R1; reword to "Λ = A⁻¹Γ_trueA⁻ᵀ, the population target of Λ̂_T (C43 for Λ*)".
- **F4.** The theorem name `oneState_signSel_coverage_eventually_lt` concludes `≤ Φ − (1 − Φ)/2`; fine (strictly
  below Φ), but the docstring should say "at most ..., hence strictly below Φ(z)".

## Recommended entry docstring (for `Formalization/Statements/Ch7.lean`)

```
/-- Corrected (fixed-shape) and oracle-restricted variant of the confidence-set rule `eq:convex.Cdelta`
(`chapters/inference.tex:189–195`, display :191–193) and of the claim that "such sets serve as approximate
confidence regions" (:196); rectangle prose :198–205. See `docs/SOURCE-ISSUES.md#C47` and `#C43`.

Differs from the printed text: (1) the printed claim for arbitrary convex sets chosen from the data is false
(C47(1); Lean evidence for the oracle variant in `TDInferenceC47Evidence711.lean`); here the direction `u` and level
`z` are fixed before the data, the C47 proposed correction. (2) The covariance is the oracle
`Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`, the population target of the printed plug-in `Λ̂_T` (:180–182), unknown in practice;
`Γ_true` is the true residual covariance, not the printed `Γ` of `Λ*` (:115, C43). The plug-in rule is not proved.
(3) Only half-lines, slabs and a Bonferroni box; the printed `ℓ∞`-quantile rectangle (C47(2)) and the ellipsoid
(C47(3)) are not addressed. `Γ_true ≻ 0` is assumed. Kept: i.i.d. sampling, full-support `μ`,
`0 < η₀ < 1/4` (:133), every `V₀`, the rate `T^{-1/3}` with an instance constant `K`.

Statement: there is one `K > 0` such that for all `T ≥ 1`, with `Φ(z) = N(0,1)(−∞, z]` and `S = |State|`:
(1) all `z ∈ ℝ`, `u ≠ 0`: `|P(uᵀV̄_T − z√(uᵀΛu/T) ≤ uᵀV^π) − Φ(z)| ≤ K T^{-1/3}`;
(2) `z ≥ 0`, `u ≠ 0`: `|P(|uᵀ(V̄_T − V^π)| ≤ z√(uᵀΛu/T)) − (2Φ(z) − 1)| ≤ 2K T^{-1/3}`;
(3) `z ≥ 0`: `P(∀ s, |V̄_T(s) − V^π(s)| ≤ z√(Λ_ss/T)) ≥ 1 − 2S(1 − Φ(z)) − 2SK T^{-1/3}`. -/
def Eq_convex_Cdelta_corrected_oracle : Prop := ...   -- body unchanged from DRAFT-STATEMENT.lean
```

## Recommended COVERAGE headline (label `eq:convex.Cdelta`)

> **Partial.** Fixed-shape correction with oracle covariance only (`Eq_convex_Cdelta_corrected_oracle`): one-sided and
> two-sided intervals for a linear functional `uᵀV^π` fixed before the data, and a Bonferroni box, with
> `Λ = A⁻¹Γ_trueA⁻ᵀ` (unknown in practice) and error `O(T^{-1/3})`. The printed claim for arbitrary data-selected
> convex sets is false (C47(1); Lean evidence for the oracle variant: `oneState_signSel_coverage_eventually_lt`). Open:
> the plug-in `Λ̂_T` rule (item D), the printed rectangle (C47(2)), the ellipsoid (C47(3)), the singular plug-in (C47(4)).

## Recommended C47 addendum

> **Lean evidence for (1), oracle covariance (2026-11-09, `Formalization/Ch7Rest/TDInferenceC47Evidence711.lean`).**
> In the one-state TD instance of (1) (π uniform over rewards 0 and 1, γ = 1/2: V^π = 1, Γ_true = 1/4, A = 1/2, oracle
> Λ = 1, all machine-checked), the sign-selected half-lines `[V̄_T − z/√T, ∞)` if V̄_T ≥ 1 and `(−∞, V̄_T + z/√T]`
> otherwise are convex, read only the data, and each has mass exactly Φ(z) = 1 − α under N(V̄_T, Λ/T)
> (`gaussianReal_signSel`). Their coverage is within 2K·T^(-1/3) of 2Φ(z) − 1 = 1 − 2α (`oneState_signSel_coverage`,
> from the half-space Theorem 7.11 result, no CLT), and is eventually at most Φ(z) − (1 − Φ(z))/2 < 1 − α for every
> z ≥ 0 (`oneState_signSel_coverage_eventually_lt`). The rule's threshold 1 equals V^π of this instance, as the paper
> witness's threshold 0 equals θ; this suffices because the printed claim is universal over such sets. Scope: oracle
> Λ, not the printed Λ̂_T; the Λ̂_T version additionally needs consistency of Λ̂_T (in this model Ā_T = 1/2 surely,
> so Λ̂_T = 4Γ̂_T). Line locators corrected against the pin: rule :187–196 (display :191–193, claim :196), rectangles
> :198–205, ellipsoids :207–213. Independently critic-reviewed (`docs/critic-confint.md`). Not author-approved.

## Scratch files (critic folder only)

`reviewer-probes/{Sanity.lean, ProbeEntryCtx.lean, ProbeFull.lean, ProbeG_copy.lean}`.
No repository edits outside this folder and this report; no git changes.
