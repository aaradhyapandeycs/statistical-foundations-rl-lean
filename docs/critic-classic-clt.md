# CRITIC: item A, classic CLT display `eqn:classic-clt` (inference.tex:98–117)

Public copy of the independent critic report; local paths removed. Probe and scratch files named below (`reviewer-probes/`, `builder-probes/`) were kept in private folders and are not published.

Post-review note (added to this public copy, 2026-11-09): the entries were integrated verbatim as `Eq_classic_clt_corrected` (with the F2 sentence appended) and `Eq_classic_clt_restricted` in `Formalization/Statements/Ch7.lean`, with wrappers in `Ch7Proofs.lean`; the three modules are imported from `Formalization.lean`; R1 (Theorem 7.11 row wording), the COVERAGE row and the C43 addendum were applied, and F3 was added to the module doc of `TDInferenceCLTPrinted711.lean`. F1 (`trueGamma` docstring in `TDInference711Defs.lean`) is deferred, since editing that definitions module would force a rebuild of every dependent. The review text below is otherwise unchanged.

Critic: independent (not the builder). Date 2026-11-09. Scratch: `reviewer-probes/`.

## Verdict: **ACCEPT WITH FIXES** (fixes are documentation only; no Lean change required)

The bridge is valid, the smooth export's hypotheses are met, the printed Props encode the display faithfully under the
C43 reading, the refutation arithmetic checks, and the restricted identity Γ_true = Γ_printed is correct. The draft
entries are honest. Required fixes concern stale COVERAGE text and two docstring nits.

## Evidence (commands actually run)

All via `bash scripts/lean-local.sh <file>`, one Lean process at a time after `pgrep -x lean | wc -l` < 2:

| File | sha256 (16) | Result |
|---|---|---|
| `Formalization/Probability/WeakConvergenceSmoothTest.lean` | 4054bb728168f829 | exit 0, no output (3 s) |
| `Formalization/Ch7Rest/TDInferenceCLT711.lean` | 52f4ff8d7b3b5b0f | exit 0, no output (3 s) |
| `Formalization/Ch7Rest/TDInferenceCLTPrinted711.lean` | 08d6f36db26d1321 | exit 0, no output (2 s) |
| `builder-probes/DRAFT-ENTRIES-ONLY.lean` (entries vs. `TDInference711Defs` + Mathlib bounded-continuous only) | — | exit 0 |
| `builder-probes/DRAFT-STATEMENT.lean` (entries + wrappers) | — | exit 0; both `_holds` axioms = [propext, Classical.choice, Quot.sound] |
| `reviewer-probes/CriticProbe.lean` (imports `Formalization` + the three modules) | — | exit 0 (67 s); all `#print axioms` = [propext, Classical.choice, Quot.sound] |

Hashes match the builder status note. The ENTRIES block in DRAFT-STATEMENT and DRAFT-ENTRIES-ONLY is textually identical
(diff only in the leading comment). `grep sorry|admit|axiom` on the three modules: no hits. Name collisions: every new
declaration name (`lawMeasure`, `lawProbabilityMeasure`, `gaussCovPM`, `diagMin_prob_pos/_le`, `zTest*`,
`tendsto_zTest_law`, `reward_eq_policyReward_of_const_on_support`, `exists_smooth_*`, `Eq_classic_clt_printed*`)
occurs only in its own file; `Eq_classic_clt_corrected/_restricted` are not yet in `Statements/Ch7.lean`.
Note: the three modules are not yet imported by `Formalization.lean` (integration step; see F1).

Critic probe contents (all proved, standard axioms):
- `critic_corrected_exists_holds`: an independently written existential-schedule reading of the corrected display
  (∃ η₀ ∈ (0,1), ∀ V₀, ∀ bcf g) follows from `tendsto_sum_pathWeight_bcf_gaussCov`.
- `not_critic_printed_someInit_open`: the printed reading with η₀ restricted to the source's step range
  (0 < η_t < 1 ⇔ η₀ ∈ (0,1), `inference.tex:75`) and some V₀ is refuted (immediate from `_someInit`).
- `z_true_limit_zero`: consistency of corrected theorem and refutation on instance Z: `∫ min(1,|x 0|) dN(0, A⁻¹Γ_trueA⁻ᵀ) = 0`
  (Γ_true = 0 there, degenerate limit), derived by `tendsto_nhds_unique` from the two independent limits.
- `z_not_in_class`: instance Z lies outside the restricted class, derived semantically (if it were inside,
  Γ_true = Γ_printed would contradict `zTest_gauss_pos` and `z_true_limit_zero`). Cross-validates the restricted lemma.
- The bridge's exact quantifier shape restated over an arbitrary `E` and closed by the export.

## (1) Bridge `tendsto_integral_bcf_of_tendsto_integral_smooth` — VALID

Reconstruction: for open G, `IsOpen.exists_smooth_support_eq` gives smooth f with support exactly G and range ⊆ [0,1].
h_k = χ_k·(1 − (1 − f)^k), χ_k a `ContDiffBump` at 0 with rIn = k+1, rOut = k+2. Smooth (product/power of smooth),
compactly supported (χ_k is), 0 ≤ h_k ≤ 1_G (off G, f = 0 so h_k = 0; on G both factors in [0,1]), and h_k(x) → 1_G(x)
(on G, f(x) > 0 so (1−f)^k → 0 and χ_k(x) = 1 once k ≥ ⌈‖x‖⌉). Then ofReal(∫h_k dμ_n) ≤ μ_n(G), take liminf in n
using the hypothesis, then k → ∞ by dominated convergence (dominator 1, ν finite) to get ν(G) ≤ liminf μ_n(G).
`tendsto_of_forall_isOpen_le_liminf'` (ProbabilityMeasure, atTop on ℕ countably generated) gives weak convergence,
then `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`. No tightness is needed: with probability measures on
both sides, the open-set Portmanteau inequality alone characterizes weak convergence (mass escape is excluded because
ν(E) = 1 ≤ liminf μ_n(E) = 1 and the standard proof is complete). Measurability: `[MeasurableSpace E] [BorelSpace E]`;
on `State → ℝ` the pi-Borel instance is found automatically (the CLT711 call compiles). `∞` is `((⊤ : ℕ∞) : WithTop ℕ∞)`
(smooth, not analytic), matching CLT711's explicit form. FiniteDimensional is used only for the smooth-support lemma and
bumps; legitimate.

## (2) `exists_smooth_test_bounds` — VALID

C^∞ ⇒ C² and C³; fderiv f is C¹ with compact support ⇒ bounded (`exists_bound_of_continuous`); fderiv(fderiv f) is
C¹ with compact support ⇒ Lipschitz (`ContDiff.lipschitzWith_of_hasCompactSupport`). This is exactly the hypothesis
shape of `scaledError_smooth_gaussian_le` (`TDInferenceSmooth711.lean:306–316`: `ContDiff ℝ 2 f`, ‖fderiv f‖ ≤ L₁,
Lipschitz Hessian with L₂). The other export hypotheses are discharged with μmin = `diagMin μ.prob` (positive under full
support, ≤ μ(s)), T ≥ 1 eventually, η₀ ∈ (0,1]. The bound L₁K T^{-1/6} + L₂C T^{-1/2} → 0 with K, C independent of T.
Correct.

## (3) Printed Props and refutation — FAITHFUL; disclosure ACCURATE

- Objects: `tdA = diag(μ)(I − γP_π)` (:114), `printedGamma` with r(s) := r_π(s) (:115, prelim :418), `gaussCov A Γ` is the law
  of A⁻¹(√Γ⊙Z), covariance A⁻¹diag(Γ)A⁻ᵀ (:108). A is invertible under full support and γ < 1, so no junk inverse.
  `scaledError` = √T(V̄_T − V^π) with V̄_T = T⁻¹∑_{t=1}^T V_t (:82, :88); `pathWeight` is the i.i.d. law (:56–61).
  Convergence in distribution is encoded as E g → ∫ g dN for every bounded continuous g on ℝ^S: the definition.
- Quantifiers: instance (finite types in `Type`, nonempty), full-support μ (λ₀ > 0, :67), "all other parameters fixed"
  = limit only in T. Extra `[Nonempty Action]`/`[DecidableEq State]` binders only weaken the ∀-Prop, so the
  refutation is not weakened by them.
- Schedule: the display says "with an appropriate choice of the learning rate schedule" (:98), an existential.
  `tdIter` fixes η_t = η₀t^{-2/3}. `Eq_classic_clt_printed` (η₀ ∈ (0,1/4), ∀V₀) and `_someInit` (∃η₀ ∈ (0,1], ∃V₀ per
  instance) are refuted. Within the family, `_someInit` is the weakest reading: both remaining parameters are
  existential per instance, and η₀ ∈ (0,1] already contains the source-admissible range η₀ ∈ (0,1) (0 < η_t < 1 at t = 1,
  :75); η₀ > 1 violates the source's step constraint. The disclosed paper argument (V₀ = V^π refutes the display for
  every schedule, because zero TD error leaves the iterate fixed for any η_t) is correct, and it is correctly labelled
  as not Lean-checked. "Some schedule and some V₀" over arbitrary schedules is correctly reported as not refuted.
- Arithmetic re-derived by hand: on Z, A = ½[[3/4,−1/4],[−1/4,3/4]], A⁻¹ = [[3,1],[1,3]]; Γ_printed,ss = ½·(±1/8)² = 1/128.
  X₀ = (3Z₀+Z₁)/(8√2) has variance 10/128, sd ≈ 0.280, so N(|X₀| ≤ 1/20) ≈ 0.143 ≤ 1/4 (`zGauss_slab_le`). Hence
  ∫ min(1,|x₀|) dN ≥ (1/20)(1 − 1/4) = 3/80 > 0. Law side: 0 ≤ E min(1,|√TΔ̄_T(0)|) ≤ E|√TΔ̄_T(0)| ≤ D·T^{-1/2} → 0
  (`zScaledError_expect_le`, any η₀ ∈ (0,1], any V₀). Uniqueness of limits closes it. Correct.

## (4) Restricted reading — CORRECT

If r(s,·) is constant on supp π(·|s), then r(s,a) = r_π(s) for every supported a. Printed:
μ(s)∑_{s'}∑_a π(a|s)P(s'|s,a)(V(s) − r_π(s) − γV(s'))²; true: μ(s)∑_a π(a|s)∑_{s'}P(s'|s,a)(V(s) − r(s,a) − γV(s'))².
Terms with π(a|s) = 0 vanish on both sides; others agree; swap sums. Lean proof follows this exactly. The class
contains state-only rewards and deterministic π (CHECK's widening request is met). It is sufficient, not necessary
(Var_a r + 2γCov(r, V^π(s')) can vanish otherwise); the docstring does not claim necessity. Good.

## (5) Entries and docstrings — HONEST, minor fixes

`Eq_classic_clt_corrected` (Γ → Γ_true, a different object: `_corrected` is right) and `Eq_classic_clt_restricted`
(printed Γ on a sub-class: `_restricted` is right). Both are self-contained Props over definition-module objects
only (compiled alone). Wrappers just apply the exports (`η₀ < 1/4 ⇒ η₀ ≤ 1`). No rate, confidence-region or
Γ ≻ 0 claim. Line citations check: display :100–103, prose :98, Λ⋆/A/Γ :104–117, η₀ < 1/4 :133.

## (6) Non-vacuity — OK

Hypotheses satisfiable (instances G, S in builder Probe; Z in critic probe). Corrected limit is genuinely degenerate on Z
(proved `z_true_limit_zero`), so "no Γ_true ≻ 0" is substantive. Restricted class is non-empty (S) and excludes Z.

## Findings

- **R1 (required, doc).** `docs/COVERAGE.md` Thm 7.11 row says the smooth partial result "does not imply … the classic
  CLT display". After this change that is stale: smooth result + bridge do imply the corrected display. Replace with
  "does not by itself imply …; with the Portmanteau bridge it yields the corrected classic CLT display
  (`Eq_classic_clt_corrected`)".
- **R2 (required, integration).** Import the three modules from `Formalization.lean` (and the entries/wrappers from
  `Statements/Ch7.lean` / `Ch7Proofs.lean`, which already import `TDInference711Defs`) so the axiom audit covers them;
  add the C43 addendum and COVERAGE row below in the same change (AGENTS statement-index rule).
- **F1 (nit).** `TDInference711Defs.lean` `trueGamma` docstring says "unused in M1"; now the CLT limit's covariance.
  Optional refresh (not owned by this item).
- **F2 (nit).** In `Eq_classic_clt_corrected` docstring, add one clause "Qualitative (no rate); no confidence-region
  statement." to pre-empt overreading. Optional.
- **F3 (nit).** `TDInferenceCLTPrinted711.lean` module doc could cite `inference.tex:75` (0 < η_t < 1) as the reason
  η₀ ∈ (0,1] exhausts the admissible family. Optional.

## Recommended entry texts

Accept the two draft entries in `builder-probes/DRAFT-STATEMENT.lean` (lines 13–78) verbatim, with
F2 optionally appended to the `_corrected` docstring after "No `Γ_true ≻ 0` hypothesis: the limit may be degenerate.":
"The statement is qualitative (no rate) and makes no confidence-region claim." Wrappers (lines 81–98) verbatim.

## Recommended COVERAGE row

| Classic CLT display, `eqn:classic-clt`, inference chapter lines 98–117 | [WeakConvergenceSmoothTest.lean](../Formalization/Probability/WeakConvergenceSmoothTest.lean), [TDInferenceCLT711.lean](../Formalization/Ch7Rest/TDInferenceCLT711.lean), [TDInferenceCLTPrinted711.lean](../Formalization/Ch7Rest/TDInferenceCLTPrinted711.lean), [Ch7.lean](../Formalization/Statements/Ch7.lean), [Ch7Proofs.lean](../Formalization/Statements/Ch7Proofs.lean) | **Printed display refuted under the C43 reading; corrected and restricted variants proved.** Corrected (`Eq_classic_clt_corrected`, export `tendsto_sum_pathWeight_bcf_gaussCov`): with Γ replaced by the true TD-noise covariance Γ_true, for every finite instance, full-support i.i.d. sampling, step sizes η_t = η₀t^(-2/3) with 0 < η₀ < 1/4 (export: 0 < η₀ ≤ 1) and every V₀, √TΔ̄_T →d N(0, A⁻¹Γ_trueA⁻ᵀ) (convergence of E g for every bounded continuous g); no Γ_true ≻ 0 is assumed, so the limit may be degenerate. Restricted (`Eq_classic_clt_restricted`): the printed Γ, when r(s,·) is constant on the support of π(·\|s) for every s (state-only rewards or deterministic π), where Γ_printed = Γ_true. Refuted (`not_eq_classic_clt_printed`, `not_eq_classic_clt_printed_someInit`): with action-dependent rewards and r(s) = r_π(s), the display fails for the step-size family η₀t^(-2/3), even for some η₀ ∈ (0,1] and some V₀ chosen per instance ([C43](SOURCE-ISSUES.md#C43)). The display's "appropriate schedule" is existential; arbitrary schedules are not covered by the Lean refutation (for V₀ = V^π the paper argument covers every schedule; "some schedule and some V₀" is not refuted). Qualitative only: no rate, no confidence regions. Proof: smooth Gaussian approximation (`scaledError_smooth_gaussian_le`) plus a Portmanteau bridge from C^∞ compactly supported tests to bounded continuous tests (no tightness needed). Not from the cited classical theory. [Review](critic-classic-clt.md). Not author-approved. |

## Recommended C43 addendum

**Classic CLT display (2026-11-09, `Formalization/Ch7Rest/TDInferenceCLT711.lean`, `TDInferenceCLTPrinted711.lean`;
entries `Eq_classic_clt_corrected`, `Eq_classic_clt_restricted`).** The same Γ issue affects `eqn:classic-clt`
(`inference.tex:98–117`). Machine-checked: with r(s) = r_π(s) and action-dependent rewards, the display is false for the
step sizes η_t = η₀t^(-2/3), both for every η₀ ∈ (0,1/4) and every V₀ (`not_eq_classic_clt_printed`) and for some
η₀ ∈ (0,1] and some V₀ per instance (`not_eq_classic_clt_printed_someInit`). Witness: the zero-noise instance above with
the bounded continuous test min(1, |x(0)|), whose expectation under the data law is O(T^(-1/2)) while under
N(0, A⁻¹Γ_printedA⁻ᵀ) it is at least 3/80. The display is existential in the schedule; the Lean refutation covers this
family only. For V₀ = V^π the iterates never move under any schedule, so that reading fails for every schedule (paper
argument, not Lean-checked). "Some schedule and some V₀" over arbitrary schedules is not refuted. Proved: with Γ replaced
by Γ_true (no nonsingularity needed) the display holds for every η₀ ∈ (0,1] and every V₀; and with the printed Γ it holds
whenever r(s,·) is constant on the support of π(·|s) for every s, since then Γ_printed = Γ_true
(`trueGamma_eq_printedGamma_of_reward_const_on_support`). This settles the state-only-reward reading for the display
(not for Theorem 7.11's convex-distance bound). Independently critic-reviewed. Not author-approved.
