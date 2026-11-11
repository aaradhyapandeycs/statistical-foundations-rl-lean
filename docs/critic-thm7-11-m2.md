# CRITIC: Theorem 7.11 M2 (`thm:Berry-Esseen-linear`): `not_thm7_11_printed_someInit`, `_someInit_instWise`, `anyInit_violates`

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this review was of the builder's pre-integration snapshot. The builder's modules were integrated as `Formalization/TDInference/Definitions.lean` (Defs), `Formalization/TDInference/PrintedStatement.lean` (Printed), `Formalization/TDInference/ZeroNoiseRefutation.lean` (ZeroNoise), `Formalization/TDInference/SomeInitVariants.lean` (SomeInitVariants), `Formalization/TDInference/PathMarginals.lean` (PathMarginals), `Formalization/TDInference/AnyInitRefutation.lean` (AnyInit), `Formalization/Probability/GaussianAntiConcentration.lean` (GaussianAntiConcentration) and `Formalization/Analysis/StepSizeSums.lean` (StepSizeSums), and module names below are given under their integrated names; the file hashes quoted below are those of the reviewed snapshot. The required docstring fix R2 was applied at integration. Theorem 7.11 is recorded as a refutation of the printed statement under the reading named below, not as a proved result, and no statement-index entry suggests a proved Theorem 7.11. The step-size file was placed under `Formalization/Analysis/` (the file location suggested in O3); the other optional items O1–O5 were not done. The review text below is otherwise unchanged.

I am an independent critic, not the builder. I read the source (`inference.tex:47–141`, `prelim.tex:410–421`), AGENTS.md,
SOURCE-ISSUES C43, the builder's private plan §1.2/§2.4/§2.7, the plan check (docs/critic-thm7-11-plan-check.md) F5/O4/O5 and the M1 critic report (docs/critic-thm7-11-m1.md), then the builder's
Lean and notes. I edited nothing except this file and the probe folder `<reviewer probe folder>/`.
No paper was fetched.

## Verdict

**ACCEPT WITH DISCLOSURES.** `not_thm7_11_printed_someInit` and `not_thm7_11_printed_someInit_instWise` are genuine
refutations of the printed theorem under the one-fixed-V₀-per-instance reading, including its weakest form (V₀, c, C̃
all chosen after the instance). The core lemma `anyInit_violates` holds for **every** V₀, every η₀ ∈ (0,1] and every
real c, C̃. Neither refuted Prop is stronger than the printed text. The one remaining reading dependency is (i)
action-dependent rewards with r(s) = r_π(s), carried over from M1. Required fixes are documentation and integration
only; no Lean signature changes.

## Evidence (commands actually run, repo root, foreground, one at a time)

- M2 snapshot: the builder's M2 snapshot hash list matches `shasum -a 256` of the five snapshot files, and `cmp` shows
  the builder's live M2 working files are identical: TDInferenceSomeInitVariants711 `27a93a26…afa7d`, StepSizeSums `7b414eaf…c8c1`,
  GaussianAntiConcentration `a4315ec7…0dbc`, TDInferencePathMarginals711 `5cea9e15…e85e`, TDInferenceAnyInit711 `eb63e76c…8330` (= the final table of the builder's build log).
- M1 snapshot: the builder's M1 snapshot hash list matches, and the builder's live M1 working files are byte-identical to the
  M1-critic-reviewed snapshot (TDInference711Defs `f8b6d4aa…8d7a`, TDInferencePrinted711 `76227d60…490b`, TDInferenceZeroNoise711 `9d048bc7…ef0612c`).
- Source pins: `inference.tex` `82707713…48f2`, `prelim.tex` `2d27bb72…31a5` (as in the builder's private plan §0 and the M1 critic report).
- Independent rebuild, not the builder's oleans: all eight files (3 M1 + 5 M2) copied to
  `<reviewer probe folder>/` under a separate module prefix, only the module prefix in the import lines changed
  (checked by `diff`), compiled in dependency order with
  `bash scripts/lean-local.sh -o <reviewer olean path>/<X>.olean <file>`: TDInference711Defs 2 s, TDInferencePrinted711 2 s,
  TDInferenceZeroNoise711 4 s, TDInferenceSomeInitVariants711 2 s, StepSizeSums 2 s, GaussianAntiConcentration 3 s,
  TDInferencePathMarginals711 2 s, TDInferenceAnyInit711 6 s; all exit 0, no errors (outputs `m2c_*.out`).
- Probe `<reviewer probe folder>/CriticProbeM2.lean` (sha `4a7911e7…1730`, output `critic-probe-m2.out`, exit 0, 10 s):
  `#print axioms` of `not_thm7_11_printed_someInit`, `not_thm7_11_printed_someInit_instWise`, `anyInit_violates`,
  both implication lemmas, `gaussCov_slab_le`, `stdGaussianPi_abs_linear_le`, `measure_pi_le_of_slice_le`: all
  `[propext, Classical.choice, Quot.sound]`. `#check` of the reusable lemmas confirms the stated signatures. Critic
  checks: Gaussian total mass 1 at Z; slab contains 0 and excludes (1,1); `lawProb … V₀ T univ = 1` for arbitrary V₀;
  `stepSize (1/8) 1 = 1/8`; and a critic-written even weaker reading (O1 below) is refuted, axioms clean.
- Token scan of the five M2 files: no `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `implemented_by`, `extern`,
  `unsafe`, `set_option`.
- Disclosures: a full project check was running (two Lean processes) during my compiles, so up to three Lean processes
  ran at once briefly. My compile logs were first written to a temporary folder and then moved into the probe folder. Nothing under
  `Formalization/` or `.lake/build/lib/lean/Formalization*` was written.

## Check 1: statements and quantifier order

`Thm7_11_printed_someInit` (M1, unchanged): `∃ c>0, ∀ instance, ∀ η₀ ∈ (0,1/4), hyps → ∃ V₀, ∃ C̃>0, ∀ T≥1, ∀ closed
convex C, |P(√TΔ̄_T∈C) − N(0,A⁻¹ΓA⁻ᵀ)(C)| ≤ c·K·T^{−1/3} + C̃·T^{−1/2}`.
`Thm7_11_printed_someInit_instWise` (new): same, with `∀ instance, ∀ η₀, hyps → ∃ V₀, ∃ c>0, ∃ C̃>0, …`.

- **Which is weakest.** Consecutive existentials commute, so "V₀ before c, C̃" and "c, C̃ before V₀" after the instance
  are the same Prop; `_instWise` covers every ordering with all three chosen per instance (and after η₀). Universal c
  (`someInit`) only strengthens the Prop. So `_instWise` is the weakest some-V₀ reading with deterministic, T-independent
  V₀, and its refutation implies every other. V₀ may even depend on η₀ here (weaker still).
- **Implication lemmas.** `someInit → someInit_instWise` (keep c) and `instWise(every V₀) → someInit_instWise`
  (V₀ := 0): directions correct, both trivial and kernel-checked.
- **Other elements** are the M1-reviewed objects (lawProb, gaussCov, printedRate, Γ_printed with r_π, closed convex
  sets only, Γ ≻ 0 hypothesis, η₀ ∈ (0,1/4)). Each either matches the printed text or weakens the Prop. Positivity of
  the witnesses c, C̃ is as printed (`≲`, `C̃>0`); `anyInit_violates` holds for all real c, C̃, so dropping positivity
  changes nothing.
- **η₀.** The Props quantify η₀ only over the printed range (0,1/4); the refutation instantiates η₀ = 1/8.
  `anyInit_violates` needs η₀ ≤ 1 only because the Lyapunov step needs η_t ∈ [0,1]; η₀ > 1 is outside the printed
  theorem, so excluding it neither weakens nor strengthens what is refuted.
- **Not covered (not reasonable readings of the printed text, disclose only):** an initialization depending on T, and a
  random V₀.

## Check 2: mathematics of R2 at instance Z (recomputed)

- Zero noise: r(s,a) + ½V^π(a) = V^π(s) on all four pairs, so Δ(s_t) ← (1−η)Δ(s_t) + ηγΔ(a_t), s, a uniform independent.
  By convexity ((1−η)x + η(y/2))² ≤ (1−η)x² + ηy²/4, so EΦ' − Φ ≤ ½Σ_s(−ηΔ_s²) + ½Σ_s ½Σ_a ηΔ_a²/4 = −ηΦ/2 + ηΦ/8
  = −(3η/8)Φ, needing η ∈ [0,1]. `zOneStep` states exactly this over the exact one-tuple law `tupleProb`.
- η_i = η₀ i^{−2/3} ∈ [0, η₀] ⊆ [0,1] for i ≥ 1 (`stepSize_succ_*`; index is i+1 ≥ 1, no 0^{−2/3} junk);
  Σ_{i=1}^t i^{−2/3} ≥ t·t^{−2/3} = t^{1/3}; 1 − x ≤ e^{−x}; so EΦ(V_t) ≤ Φ₀ exp(−(3/8)η₀ t^{1/3}). Correct.
- First moment: |y| ≤ y²/(2δ) + δ/2 with δ = exp(−(3η₀/16)t^{1/3}), δ² = exp(−(3/8)η₀t^{1/3}), gives
  E|V_t(0) − 1| ≤ (Φ₀+1)δ/2. Correct.
- Averaging: (√TΔ̄_T)(0) = T^{−1/2}Σ_{t=1}^T(V_t(0) − 1) (`zScaledError_apply_zero`, using M1's
  `zValueFixedPoint`, the uniqueness characterization, so V^π is genuine). Prefix marginalization moves each term to its
  own path length. Σ_t exp(−c t^{1/3}) ≤ 720/c⁶·Σ 1/t² ≤ 1440/c⁶ with c = 3η₀/16 > 0. So
  E|(√TΔ̄_T)(0)| ≤ D′/√T, D′ = (Φ₀+1)/2·1440/(3η₀/16)⁶. Correct.
- Markov on the single coordinate: P(|X(0)| ≤ ε) ≥ 1 − D′/(ε√T). Correct (indicator argument over the finite path sum).
- Gaussian side. A⁻¹ = [[3,1],[1,3]] (proved by `inv_eq_left_inv`, so not the junk 0). The true marginal of coordinate 0
  of N(0, A⁻¹ΓA⁻ᵀ) has variance (9+1)/128 = 10/128, so the exact slab mass is P(|N(0,10/128)| ≤ 1/20) ≈ **0.1420**.
  The builder does not use the marginal; it conditions on Z₁ and bounds the Z₀-slice of width 2ε/|3√(1/128)| by the
  density sup 1/√(2π): bound 2ε/(3√(1/128)√(2π)) = 4/(15√π) ≈ **0.1504** ≥ 0.1420. This is a valid upper bound (dropping
  the Z₁ contribution only enlarges the bound), and 0.1504 ≤ 1/4 (via q² = 9π/64, π ≥ 2). Correct.
- Gap on the closed convex slab {|x(0)| ≤ 1/20}: ≥ 1 − 20D′/√T − 1/4 = 3/4 − D/√T with D = 20D′. `exists_rhs_lt_one`
  (M1-reviewed, all real a, b) applied to (4/3)a, (4/3)(C̃ + D) gives a T ≥ 1 with RHS < 3/4 − D/√T. Hence
  RHS < gap for every V₀, η₀ ∈ (0,1], c, C̃ ∈ ℝ. Correct.
- Junk-value audit: T ≥ 1 everywhere rpow appears with negative exponents; `(√T)⁻¹ = T^{−1/2}` uses
  `Real.sqrt_eq_rpow`, `rpow_neg` with T ≥ 0; divisions are by δ > 0, ε = 1/20, (3η₀/16)⁶ > 0; `Measure.map_apply` uses
  M1's `measurable_gaussMap` and a measurable slab; `.real` is taken of a probability measure on a measurable set;
  `lawProb` is a finite sum with total mass 1. No junk.
- Size: D ≈ 8.7·10¹³ already for Φ₀ = 0, η₀ = 1/8, so the witness T is ~10²⁸; harmless, everything is symbolic.

## Check 3: axioms and forbidden tokens

PASS (see Evidence). Matches the builder's axiom probe output.

## Check 4: library quality

Good overall: real general statements, no theorem-specific hypotheses in the reusable lemmas.
- `GaussianAntiConcentration.lean` (`gaussianPDFReal_le_inv_sqrt`, `gaussianReal_Icc_le`, `gaussianReal_abs_affine_le`,
  `measure_pi_le_of_slice_le`, `stdGaussianPi_abs_linear_le`): general, Mathlib-style names, belongs in
  `Formalization/Probability/`. The pdf sup bound is not in the pinned Mathlib (grep of the pinned sources found none).
- `TDInferencePathMarginals711.lean`: general TD path-law lemmas and `gaussCov_slab_le` for any finite MDP; belongs in
  `Formalization/Ch7Rest/`.
- `StepSizeSums.lean`: correct and general, but these are real-analysis facts (see O3).

## Required fixes

- **R1. C43 addendum.** Replace the M1-critic-required addendum with the text below. Relative to the M1 text, it adds
  the some-V₀ refutations and deletes "and the reading with one fixed V₀ per instance (e.g. V₀ = 0), whose refutation
  is planned but not yet machine-checked". It keeps reading (i) disclosed.
- **R2. Qualify the M2 docstrings at integration.** The `TDInferenceAnyInit711.lean` header title "Theorem 7.11 is false
  for every fixed initialization" and the `not_thm7_11_printed_someInit` docstring must say "under r(s) = r_π(s) with
  action-dependent rewards" in the title or first sentence (the docstring mentions `r(s) = r_π(s)` but as a side
  clause). Documentation only.
- **R3. Integration.** Rewrite the snapshot module prefixes to `Formalization.Ch7Rest.` (TD files) and
  `Formalization.Probability.` (Gaussian file; step-size file per O3). Re-run the axiom audit on the integrated names.
  Record 7.11 in COVERAGE / named-result-status as "printed refuted (every-V₀ and some-V₀ readings; r(s) = r_π(s)
  reading); corrected theorem open". Do not add a `Thm7_11` statement-index entry suggesting a proved result.

## Optional findings

- **O1.** "For some 0 < η₀ < 1/4" could be read as η₀ also chosen per instance. My probe `critic_not_someEta_someInit`
  (∀ instance, ∃ η₀ ∈ (0,1/4), ∃ V₀, c, C̃) is refuted in five lines from `anyInit_violates`, axioms clean. Consider
  adding it as a library corollary, so the weakest reading also covers the step-size parameter.
- **O2.** `sum_range_inv_succ_sq_le_two` duplicates Mathlib's `sum_Ioo_inv_sq_le` (`Mathlib/Analysis/PSeries.lean:382`,
  k = 0) up to reindexing; consider deriving it from that, or citing it in the docstring.
- **O3.** `StepSizeSums.lean` is real analysis in namespace `StatisticalRL.Probability`; consider
  `Formalization/Analysis/StepSizeSums.lean` with a matching namespace. `Fintype.sum_fin_succ_snoc` sits in Mathlib's root
  `Fintype` namespace (future name-clash risk); consider a project namespace. The theorem names `zOneStep`, `zA_inv`
  are lowerCamel; Mathlib convention for theorems is snake_case (for example `zLyap_tdStep_expect_le`). This is
  consistent with M1's accepted `z*` names, so it is cosmetic.
- **O4.** The docstring step 5 could note that the conditioning bound 4/(15√π) ≈ 0.150 dominates the exact marginal
  mass ≈ 0.142 (variance 10/128), to save future readers the recomputation.
- **O5.** Plan-check O5 (liminf d_cvx = 1 via shrinking slabs) is not formalized; not needed for the refutation.

## Required C43 addendum text (replaces the M1-critic text)

"Machine-checked (2026-11-08, `Formalization/TDInference/ZeroNoiseRefutation.lean` and
`Formalization/TDInference/AnyInitRefutation.lean`): Theorem 7.11 is false under the reading in which rewards depend on
(s,a) as printed at `inference.tex:62` and the undefined r(s) in Γ is r_π(s) (`prelim.tex:418`). This holds whether
the bound must hold for every initialization V₀ (`not_thm7_11_printed`; also with the constants c and C̃ chosen per
instance, `not_thm7_11_printed_instWise`, and over all convex sets, `not_thm7_11_printed_allConvex`) or only for one
V₀ chosen per instance, such as V₀ = 0 (`not_thm7_11_printed_someInit` with a universal c, and
`not_thm7_11_printed_someInit_instWise` with V₀, c and C̃ all chosen after the instance, the weakest such reading).
Instance: S = A = 2, γ = 1/2, μ and π uniform, s′ = a deterministically, r = (1/2, 3/4; 0, 1/4), η₀ = 1/8. Then
V^π = (1, 1/2) and r(s,a) + γV^π(s′) = V^π(s) on every sample. From V₀ = V^π the TD iterates never move, so
√T Δ̄_T = 0 surely. The printed Γ is diag(1/128, 1/128) ≻ 0 and A = diag(μ)(I − γP_π) is invertible
(A⁻¹ = [[3,1],[1,3]]), so N(0, A⁻¹ΓA⁻ᵀ)({0}) = 0 and the convex distance is 1 at every T ≥ 1 (on the closed
convex set {0}). From any other fixed V₀, the error satisfies E‖V_t − V^π‖² ≤ ‖V₀ − V^π‖² exp(−(3/8)η₀t^{1/3}), so
E|(√T Δ̄_T)(0)| = O(T^{−1/2}). The data law therefore puts mass ≥ 1 − O(T^{−1/2}) on the closed convex slab
{x : |x(0)| ≤ 1/20}, while the printed Gaussian gives it mass ≤ 4/(15√π) < 1/4, so the convex distance is
≥ 3/4 − O(T^{−1/2}) (`anyInit_violates`, for every V₀, every η₀ ∈ (0,1] and every real c, C̃). In both cases the
printed right-hand side tends to 0 for any finite constants. No CLT is used. The example also shows that the printed
Γ omits a cross term as well as the action-reward variance: Γ_true,ss = Γ_printed,ss + μ(s)[Var_a r(s,a) +
2γ Cov(r(s,a), V^π(s′))], and here Γ_true = 0 < Γ_printed. Not refuted by this example: the reading with state-only
rewards (or deterministic π), where Γ_printed equals the true noise covariance, and the corrected statement (here
Γ_true = 0, so it is vacuous). Independently critic-reviewed. Not author-approved."

(Integration note: if the integrated file names differ, adjust the two paths; the theorem names are as in the
snapshot.)

SHA-256 of this file: reported in the critic's hand-off message (computed after writing).
