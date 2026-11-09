# Plan check: the private Chapter 7 inference plan (2026-11-09)

Public copy of the independent plan check; local paths removed. Working folders named in the original were private and are not published.

Independent critic. Read-only: no Lean compiled, no repo edits besides this file, no git changes.
Source: `source/upstream/tex/chapters/inference.tex`, SHA-256
`82707713adb6c9296d9ee41faa84b2d0a12eaf1b34864a6d294de02132e648f2` (same as the C47 pin). Mathlib was read at
the read-only Mathlib dependency checkout (commit `32d24245c7a12ded17325299fd41d412022cd3fe`, 2025-12-14), which is the
`lake-manifest.json` pin. Toolchain `v4.27.0-rc1`.

## Verdicts

| Item | Verdict | One line |
|---|---|---|
| A, classic CLT display | **GO WITH FIXES** | The maths is sound and needs no tightness hypothesis. A simpler bridge than inner regularity plus manifold Urysohn exists. The refutation's schedule scope must be disclosed, and the restricted hypothesis can be widened. |
| B, oracle intervals | **GO WITH FIXES** | B1, B2 and B3 are correct. The entry must not use `stdCDF` (the G2 import gate). It must not close the `eq:convex.Cdelta` node as proved: its COVERAGE headline must say "Partial". |
| C, plug-in Λ̂_T | **GO WITH FIXES** | The dominance computation, singular event, Γ̂ diagonal form and T^{-1/2} rate are correct. Matrix `‖·‖` has no global instance, so state norms explicitly. Add a cheap Λ̂ inconsistency refutation. The C3 estimate is low. |
| D, plug-in coverage | **GO WITH FIXES** | Correct. Name the entry `_corrected` and disclose its restriction. The junk-inverse event is automatically inside Eᶜ when δ < 1. |
| E, C47 evidence | **GO WITH FIXES** | E2 and E3 are correct. E1 should use the one-state instance, which needs no ℓ∞ quantile. E2 with oracle Λ is evidence against a variant, not the printed Λ̂ rule, until the Λ̂ version is done. |
| F, G | GO (defer), as planned | Fix F's line reference (:129, not :122). |

## (1) Mathlib claims, verified by grep at the pin

- **Absent, confirmed.** There is no Lévy continuity theorem: `charFun` appears only in `MeasureTheory/Measure/CharacteristicFunction.lean`, `IntegralCharFun.lean`, the Gaussian files and `Independence/CharacteristicFunction.lean`, with no `tendsto…charFun` theorem. There is no Cramér–Wold: "Cramer" hits only Cramer's rule in `LinearAlgebra/Matrix`. There is no Prokhorov compactness theorem. `TightNormed.lean` has only tightness characterizations (`isTightMeasureSet_iff_tendsto_measure_norm_gt`, `…_inner_tendsto`), and `LevyProkhorovMetric.lean` is the metric only.
- **Present, confirmed:**
  - `MeasureTheory.tendsto_of_forall_isOpen_le_liminf` (`Portmanteau.lean:589`). It takes `ProbabilityMeasure`s and `[L.IsCountablyGenerated]`.
  - `tendsto_iff_forall_lipschitz_integral_tendsto` (`:667`).
  - `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` (`ProbabilityMeasure.lean:346`), in the `Ω →ᵇ ℝ` Bochner form.
  - `exists_smooth_tsupport_subset` (`BumpFunction/FiniteDimension.lean:45`). It gives `f x = 1` at a single point only.
  - `IsOpen.exists_smooth_support_eq` (`:79`): support exactly `s`, `ContDiff ℝ ∞`, range in `[0,1]`.
  - The instance `HasContDiffBump E` for every finite-dimensional `E` (`:461`), so `ContDiffBump` works on `State → ℝ` with the sup norm.
  - `exists_smooth_zero_one_of_isClosed` (`Geometry/Manifold/PartitionOfUnity.lean:490`), which returns a bundled `C^∞⟮I, M; 𝓘(ℝ), ℝ⟯`.
  - `HasCompactSupport.fderiv` (`FDeriv/Const.lean:377`), `tendsto_integral_of_dominated_convergence`, and `Matrix.det_ne_zero_of_sum_row_lt_diag` (`LinearAlgebra/Matrix/Gershgorin.lean:63`), plus its column version at `:73`.
- **New finding (affects C):** matrix norms are not global instances. In `Analysis/Matrix/Normed.lean` they are `protected def`s with `local instance` / `scoped instance` (`open scoped Matrix.Norms.Operator`, `.Elementwise`, `.Frobenius`). So the plan's `‖lambdaHat − Λ‖` in a statement does not elaborate without an `open scoped`. See the C fixes.

## (2) The smooth → weak-convergence bridge (A1–A3)

**The argument is complete. No tightness hypothesis is needed.** The open-set Portmanteau criterion only needs every
μₙ and ν to be probability measures; tightness of (μₙ) is then a consequence, not an input. Here:
- each `lawMeasure T` is a finite Dirac sum with total mass `∑ pathWeight = 1`; this holds also at T = 0, where the empty product is 1;
- `gaussCov A Γ` is a probability measure for any Γ (`gaussCov_isProbabilityMeasure`), so degenerate Γ_true is fine.

For open G and any smooth compactly supported h with 0 ≤ h ≤ 1_G, μₙ(G) ≥ ∫h dμₙ → ∫h dν. So ν(G) ≤ liminf μₙ(G) once
sup_h ∫h dν = ν(G).

**Recommended simpler route (replaces the inner regularity and manifold Urysohn steps, and the plan's risk (i)).**
1. Take `f` from `IsOpen.exists_smooth_support_eq` (support = G, values in [0,1]).
2. Take `χ_k` the `ContDiffBump` at 0 with `rIn = k+1` and `rOut = k+2`. It is 1 on `closedBall 0 (k+1)` and has compact support.
3. Put `h_k := χ_k · (1 − (1 − f)^k)`. It is smooth (product of smooth functions; polynomial in f), compactly supported (`HasCompactSupport.mul_left`), takes values in [0,1], and vanishes off G.
4. Pointwise `h_k → 1_G`: on G, f ∈ (0,1] and χ_k is eventually 1; off G, h_k = 0.
5. Dominated convergence with bound 1 gives `∫h_k dν → ν(G)`.

This needs neither `InnerRegular`, `𝓘(ℝ,E)` nor `contMDiff_iff_contDiff`. The estimate for A1 drops to about 150–300 lines.

**A2.** For `ContDiff ℝ ∞ f` with `HasCompactSupport f`:
- `fderiv ℝ f` is continuous with compact support, so it is bounded; this gives `L₁`.
- `fderiv ℝ (fderiv ℝ f)` is C¹ with a continuous, compactly supported derivative, so it is bounded and hence `L₂`-Lipschitz. Use the mean value theorem on `univ` (`Convex.norm_image_sub_le_of_norm_fderiv_le`), which needs `Differentiable` of the second derivative; this follows from `ContDiff ℝ ∞` via `ContDiff.fderiv_right`.
- `ContDiff ℝ ∞ → ContDiff ℝ 2` is `ContDiff.of_le` (the order lives in `WithTop ℕ∞` at this pin).

The hypothesis forms of `scaledError_smooth_gaussian_le` (`TDInferenceSmooth711.lean:306`) are exactly `ContDiff ℝ 2 f`,
`∀ x, ‖fderiv ℝ f x‖ ≤ L₁` and `∀ x y, ‖fderiv ℝ (fderiv ℝ f) x − … y‖ ≤ L₂ * ‖x − y‖`.

**Rate sufficiency.** Yes. The constants `smoothRemainderConst M π V₀ μmin η₀` and `smoothLindebergConst M π μ μmin`
do not depend on f, and per-f convergence would be enough even if they did. `T^{-1/6}, T^{-1/2} → 0`
(`tendsto_rpow_neg_atTop`), and the bound holds for every T ≥ 1. The smooth export has no `Γ_true ≻ 0` hypothesis, so
the corrected entry correctly omits it.

**A4** (`trueGamma = printedGamma` under state-only rewards) is short. `policyTransition π s = (π s).bind (M.transition s)`
(`Formalization/MDP/Basic.lean:136`), and `policyTransition_prob` is `rfl`. The builder needs only a bind-expectation lemma.

## (3) Entry naming and classification for A

- `Eq_classic_clt_corrected` (Γ → Γ_true, any rewards) and `Eq_classic_clt_restricted` (printed Γ, restricted MDP class)
  fit the AGENTS rules and the `classify` name markers in `scripts/gen_nodes.py`. The printed display (`inference.tex:100–103`, prose :98)
  is ambiguous because r(s) is undefined, and it is refuted under the C43 reading. So neither entry may be called printed.
- **The restricted reading is honest.** Under state-only rewards, r(s) is unambiguous, Γ_printed = Γ_true exactly, full
  support μ is printed (:67), and η₀t^{-2/3} is an "appropriate schedule". The display is existential in the schedule, so
  universal over the family is stronger. **Recommended widening** (optional but cheap): use the hypothesis
  `∀ s a a', 0 < (π s).prob a → 0 < (π s).prob a' → M.reward s a = M.reward s a'`, i.e. the reward is constant on the
  support of π(·|s). This covers state-only rewards and deterministic π, which is exactly the C43 scope note's
  "not refuted" reading, and the A4 proof is unchanged. If the lead keeps state-only rewards only, the docstring must say
  deterministic π is not covered.
- **Required fix (refutation scope).** Display 7.38 says "with an appropriate choice of the learning rate schedule", an
  existential over all schedules. `tdIter` is hard-wired to η₀t^{-2/3}, so `not_eq_classic_clt_printed(_someInit)` refutes
  the display only within that family. For V₀ = V^π the zero-noise argument works for every schedule (paper level,
  trivial). The reading "∃ schedule ∃ V₀" over arbitrary schedules is **not** refuted (in zMDP a pathological summable
  schedule leaves a random nonzero limit error, and nothing rules out exotic behaviour). Exact text for both refutation
  docstrings and the C43 addendum:
  > "Refutes the display for the printed step-size family η_t = η₀t^{-2/3} (η₀ ∈ (0,1/4) for every V₀; η₀ ∈ (0,1] and
  > some V₀ for `_someInit`). The display is existential in the schedule; for V₀ = V^π the same zero-noise argument
  > refutes it for every schedule (paper argument, not Lean-checked, since `tdIter` fixes the schedule). The reading
  > 'some schedule and some V₀' over arbitrary schedules is not refuted."
- **Simplification.** `Eq_classic_clt_printed_someInit` (∃ η₀ ∈ (0,1], ∃ V₀) is implied by `Eq_classic_clt_printed`
  (∀ η₀ ∈ (0,1/4), ∀ V₀; take η₀ = 1/8). So prove `not_…_someInit` with the test `g(x) = min(1, |x 0|)`:
  E g(law) ≤ E|√TΔ̄_T(0)| → 0 by `zScaledError_expect_le`, while ∫g dN ≥ (1/20)(3/4) by `zGauss_slab_le`. Then derive
  `not_eq_classic_clt_printed` in one line. The V₀ = V^π / δ₀ proof is not needed.
- Both names match the `not_…_printed…` pattern, which G4 and gen_nodes pick up. With an entry plus a COVERAGE row the node
  becomes proved (corrected, restricted), and the refutations are listed as data. This is correct.
- Imports: the Prop uses `BoundedContinuousFunction`. If it is not already in scope via
  `TDInference711Defs → Mathlib.Probability.Distributions.Gaussian.Real`, add a **Mathlib** import such as
  `Mathlib.Topology.ContinuousMap.Bounded.Basic` to `Statements/Ch7.lean`. G2 tracks only `Formalization.*` edges
  (`scripts/static_gates.py` `gate_g2`), so this does not grow the frozen list.

## (4) Item B

Correctness, verified:
- **B1.** For T ≥ 1 and q ≥ 0: `uᵀV̄ − z√(q/T) ≤ uᵀV^π ⇔ uᵀ√TΔ̄ ≤ z√q`. Then `gaussCov_real_halfSpace` and
  `gaussianReal_real_Iic_eq_stdCDF` give Φ(z) when q > 0. q > 0 follows from u ≠ 0, A invertible and Γ_true ≻ 0. The
  error is K T^{-1/3}, valid for **all** z ∈ ℝ.
- **B2.** For z ≥ 0: slab = H(u, z√q) \ {uᵀx < −z√q}, and the second set is the complement of the closed H(−u, z√q).
  Additivity of `lawProb` and of the measure gives P(slab) = P(H(u)) − 1 + P(H(−u)). The Gaussian side is
  Φ(z) − 1 + Φ(z) = 2Φ(z) − 1, with the same q for −u. The error is ≤ 2K T^{-1/3}. Correct.
- **B3.** P(fail_s) = 1 − P(slab_s) ≤ 2(1 − Φ(z)) + 2K T^{-1/3}. A union over S coordinates gives
  ≥ 1 − 2S(1 − Φ(z)) − 2SK T^{-1/3}, with Λ_ss = ∑_r (A⁻¹_{sr})² Γ_r > 0. Correct. It is a Bonferroni box, not the printed
  ℓ∞-quantile box, and the plan says so.

Required fixes:
1. **Import gate.** `Statements/Ch7.lean` does not import `Formalization.Probability.SteinGaussian`, and the G2 list
   `scripts/gates/g2_statement_imports.txt` "may only shrink" (growth needs `--allow-grow`). Exact instruction: "State the
   entry with `(gaussianReal 0 1).real (Set.Iic z)` in place of `stdCDF z`; do not add a `Formalization.*` import to
   `Statements/Ch7.lean`." `gaussianReal` is already in scope through `TDInference711Defs`.
2. **Quantifier split.** The one-sided clause takes `∀ z : ℝ`; the two-sided clause (and B3) takes `0 ≤ z`. The sketch
   currently puts `0 ≤ z` on both.
3. **Status honesty (C47(1)).** u and z are bound outside the path sum, so the set's shape is fixed before the data and
   C47(1) does not apply. That is honest, but the printed rule's substance is the plug-in Λ̂_T, and the oracle Λ is not a
   usable procedure. If `Eq_convex_Cdelta_restricted_oracle` is attached to `label:eq:convex.Cdelta`, the COVERAGE row
   headline must begin "**Partial.**" so that the gen_nodes fail-closed rule marks the node `partial`, not proved
   (restricted). Upgrade it only when D lands. Docstring sentence:
   > "Oracle covariance Λ = A⁻¹Γ_trueA⁻ᵀ (unknown in practice), fixed direction u and level z chosen before the data;
   > linear-functional half-lines, slabs and a Bonferroni box only. The printed rule with Λ̂_T and arbitrary
   > data-selected convex sets is not proved (C47(1)); the printed rectangle (C47(2)) and ellipsoid (C47(3)) are not
   > addressed; Γ_true ≻ 0 is assumed."
   An alternative that the lead may prefer: record B as a library result plus a COVERAGE note only, with no entry, until D.

## (5) Item C

- **C2 is correct.** Row s of Ā_T has diagonal (n_s − γm_ss)/T and off-diagonal entries −γm_{sj}/T, where m_{sj} counts
  t with s_t = s and s'_t = j. So diag − ∑|off| = (1−γ)n_s/T > 0 iff n_s > 0, using `discount_lt_one` (`MDP/CoreDefinitions.lean:39`). An
  unsampled state gives a zero row and det = 0. So the matrix is singular iff some state is unsampled.
  P(singular) ≥ (1−μ(s))^T > 0 for S ≥ 2 with full support, and is ≤ ∑_s (1−μ(s))^T; for S = 1 and T ≥ 1 it is never singular. Requires T ≥ 1, since at T = 0, Ā = 0.
- **Γ̂ diagonal form:** (A_tV̄ − b_t) = e_{s_t}(V̄(s_t) − γV̄(s'_t) − r_t). This is correct, and
  E Γ̂(V^π) = (∑w)·Γ_true = Γ_true, consistent with C43.
- **Rate C ε⁻² T^{-1/2} (ε ≤ 1):** valid, not sharp.
  - The substitution step with first-moment Markov gives ε⁻¹T^{-1/2}.
  - Chebyshev steps give ε⁻²T^{-1}.
  - E‖Δ̄_T‖² = O(1/T) follows from `weightedL2_scaledError_sub_prGaussPart_le_rpow` plus the prGaussPart second moment.
  - The pathwise bound `abs_tdIter_sub_le` is deterministic (`tdPathBound`), so Γ̂ is bounded and the square is Lipschitz on that range.
  - Inverse perturbation: if A is invertible and ‖Ā − A‖ < 1/‖A⁻¹‖ then Ā is invertible. So the singular (junk) event is
    automatically inside {‖Ā − A‖ ≥ c}, and no separate charge is needed.
- **Required fix, norm.** State C3 and the C-entries with an explicit norm, not bare `‖·‖` on `Matrix`. Recommended
  self-contained form: `∀ s s', |lambdaHat … s s' − Λ s s'| ≤ …`, or the event
  `{ω' | ε < ∑ s, ∑ s', |(lambdaHat … ω' − Λ) s s'|}`. Inside proofs, use one scoped norm
  (`open scoped Matrix.Norms.Operator`) throughout.
- **Junk value.** Lean's `Matrix.inv` is `Ring.inverse det • adjugate`, which is 0 on singular Ā, so Λ̂ = 0 there. Every
  C, D and E docstring that mentions Λ̂ must say: "On the event that some state is unsampled, Ā_T is singular and the
  printed Λ̂_T is undefined (C47(4)); Lean's `Matrix.inv` returns 0 there, so `lambdaHat = 0` on that event, whose
  probability is charged in the bound."
- **Add (cheap, strong C43 evidence):** in zMDP with V₀ = V^π every residual V̄(s) − r − γV̄(s') is 0 on the support, so
  Γ̂_T = 0 and Λ̂_T = 0 surely for every T ≥ 1, while Λ⋆_printed ≠ 0. A Lean statement
  `not_eq_defn_hat_Lambda_printed_consistent` ("Λ̂_T → Λ⋆_printed in probability" is false under the C43 reading) is about
  40–80 lines after the defs. Under that reading the "estimator of Λ⋆" wording is false, so the C3 entry, if any, must
  be `Eq_defn_hat_Lambda_corrected` (target A⁻¹Γ_trueA⁻ᵀ) and cite C43 and C47(4).
- **C4 (online).** The plan's statistic is right and the triviality caveat is essential. The lifted factor
  2/(T(T+1)) is a function of T. The per-(s, s') sums of t·1[s_t = s, s'_t = s']·{1, r_t} and the per-s sums of
  t·1[s_t = s]·{1, r_t, r_t²} suffice: e_{s'}e_{s'}ᵀ is diagonal, so the size is O(S²), not O(S³). Add the
  unweighted counts n(s, s') for Ā, the current iterate V_t and the running sum ∑V_t. The required formal shape is a
  **fixed type** σ (independent of T and of the history), `init : σ`, `update : ℕ → σ → Tuple → σ`,
  `readout : ℕ → σ → (State → ℝ) × Matrix`, with `readout T (foldl update init ω) = (prAverage …, lambdaHat …)` for every
  T and ω, including the junk-inverse value. Keep it as a COVERAGE prose note; its priority is low.
- **Estimate.** C3 at 600–900 lines is optimistic given the matrix-norm bookkeeping, the weighted Γ̂ second moment and the
  substitution step. Plan for 800–1300 lines and 18–26 h.

## (6) Items D and E

- **D is correct.** On E = {|q̂ − q| ≤ δq} with z ≥ 0, the event lies between the closed half-spaces at
  z√(q(1∓δ)) (mirrored for z < 0), so |P − Φ(z)| ≤ K T^{-1/3} + |Φ(z√(1±δ)) − Φ(z)| + P(Eᶜ). The one-sided case needs only
  K, not 2K; 2K is for the two-sided case. The Φ term can be made uniform in z (sup_z |z|φ(z) < ∞), which is simpler than
  c|z|δ.
  - q̂ ≥ 0 always, since Γ̂ is a nonnegative diagonal and Λ̂ is PSD.
  - On the singular event q̂ = 0, so |q̂ − q| = q > δq for δ < 1, i.e. it lies in Eᶜ.
  - C3 gives P(|q̂ − q| > δq) → 0 for fixed δ, using |q̂ − q| ≤ (max|u|)²·∑∑|Λ̂ − Λ|. Then δ ↓ 0 gives the limit.
  - Naming: use `Eq_convex_Cdelta_corrected` (the name marker wins in `classify`). The docstring discloses the
    linear-functional shape fixed before the data, Γ_true ≻ 0, asymptotic coverage only, the junk inverse, and that
    C47(2)–(3) remain open.
- **E2 is correct for the oracle variant.** One state, π uniform, r = (0, 1) (allowed: rewards in [0,1],
  `MDP/CoreDefinitions.lean:35–36`), γ = 1/2: V^π = 1, Γ_true = 1/4 > 0, A = 1/2, Λ = 1. Choose the half-line by the sign
  of V̄_T − 1. The constant 1 is a fixed number, not knowledge of V^π: the rule is a fixed function of the data. Coverage =
  P(|√TΔ̄| ≤ z), within 2K T^{-1/3} of 2Φ(z) − 1.
  - Required fixes: (a) avoid quantiles by stating it for every z > 0 with α := 1 − Φ(z). Prove that each selected set has
    conditional mass Φ(z) = 1 − α under N(V̄_T, Λ/T), and that the coverage tends to 2Φ(z) − 1 < Φ(z).
  - (b) Docstring: "refutes the rule with the oracle covariance; the printed Λ̂_T version additionally needs
    consistency of Λ̂_T." In this one-state model Ā_T = 1/2 surely and is never singular, and Λ̂_T = 4Γ̂_T. A
    scalar Γ̂ → 1/4 argument may be cheaper than waiting for the full C3.
- **E1, required fix.** Use the same one-state instance. The ℓ∞ quantile of N(0, Λ/T) is then z√(Λ/T) via Φ, so no
  ℓ∞-quantile definition is needed. The half-width is z√Λ/T. Coverage ≤ N(0, Λ)([−z√Λ/√T, z√Λ/√T]) + 2K T^{-1/3} → 0.
  Disclose that it is the oracle and S = 1 version of C47(2).
- **E3** follows directly from C2. **E4** (χ²) stays a paper calculation. Agreed.

## (7) Estimates, order and locators

- A falls to about 600–1000 lines with the simpler bridge. C rises (see above). The total is unchanged in order of
  magnitude.
- **Order fix.** Move E3 and the new Λ̂-inconsistency refutation directly after C-defs + C2, before C3. They are cheap and
  machine-check C47(4) and C43. Wave 1 is A, B, and C-defs/C2/E3. A full `check.py` is currently using both Lean slots, so
  builders queue their compiles (at most two concurrent Lean compilers in total, including the lead's).
- **Locator fixes** (plan and C47 addendum):
  - `d_cvx ≤ TV` is at `:129`, not `:122`.
  - The `eqn:classic-clt` display is `:100–103`, with the prose at `:98`.
  - The `eq:convex.Cdelta` rule is `:191–193`, plus `:194–196`.
  - In C47 the printed ranges are off by about 2 lines: `eq:defn-hat-Lambda` is `:180–182`, not `:179–181`; rectangles
    `:198–205`, not `:196–203`; ellipsoids `:207–213`, not `:205–213`; the rule `:187–196`, not `:185–194`. Correct them in
    the C47 addendum.

## Recommended first builder briefs

**Builder 1: `thm7_11-clt` (Item A).** Use the plan §4 brief with these changes:
- In A1, use the `IsOpen.exists_smooth_support_eq` × `ContDiffBump` × `(1 − (1 − f)^k)` route with dominated convergence. The inner-regularity and manifold Urysohn routes are fallbacks only.
- Export `not_eq_classic_clt_printed_someInit` and derive `not_eq_classic_clt_printed` from it.
- Draft the A4 hypothesis as reward constant on the support of π(·|s), or justify keeping state-only rewards.
- Add the schedule-scope docstring text from (3).

Owned new files:
- `Formalization/Probability/WeakConvergenceSmoothTest.lean`
- `Formalization/Ch7Rest/TDInferenceCLT711.lean`
- `Formalization/Ch7Rest/TDInferenceCLTPrinted711.lean`
- WIP in a private working folder.

Validation: as in the plan (`scripts/lean-local.sh -o …`, one compile at a time, axiom probe, forbidden-token grep).
Stop: all three files compile, and the axioms of `tendsto_sum_pathWeight_bcf_gaussCov`, the restricted corollary and both
refutations are only `propext`, `Classical.choice` and `Quot.sound`. Hand back the export signatures and the draft
docstrings for `Eq_classic_clt_corrected` / `_restricted`.

**Builder 2: `thm7_11-confint` (Item B, then E2 and E1 oracle).**
- Owned: `Formalization/Ch7Rest/TDInferenceConfInt711.lean` (B1–B3); later `Formalization/Ch7Rest/TDInferenceC47Oracle711.lean` (E2, E1 on the one-state instance). WIP in a private working folder.
- Imports: `TDInferenceHalfSpace711` (and `SteinGaussian` in library files only).
- Exports: `abs_coverage_oneSided_sub_stdCDF_le` (∀ z), `abs_coverage_twoSided_sub_le` (z ≥ 0) and `coverage_rect_bonferroni_ge`, with K taken once from `abs_lawProb_halfSpace_sub_gaussCov_le`.
- Draft entry text with `(gaussianReal 0 1).real (Set.Iic z)`, and the "Partial" COVERAGE headline text.
- Stop: B compiles and its axiom probe is clean. Then continue to E2/E1 only on the lead's go.

**Builder 3: `thm7_11-covest` (Item C, phase 1).**
- Owned: `Formalization/Ch7Rest/TDInferenceCovEst711Defs.lean` (`aBar`, `wT`, `gammaHat`, `lambdaHat`, all for T ≥ 1 and documented at T = 0) and `Formalization/Ch7Rest/TDInferenceCovEstSingular711.lean`. WIP in a private working folder.
- Phase-1 exports:
  - C1 `sum_wT = 1`;
  - C2 `aBar_det_ne_zero_iff` (all states sampled) and `exists_lawProb_aBar_singular_pos` (S ≥ 2, full support);
  - E3 the C47(4) witness;
  - `not_eq_defn_hat_Lambda_printed_consistent` (zMDP, V₀ = V^π, Λ̂ = 0 surely).
- Norms: entrywise `|· s s'|` only in statements.
- Stop: phase-1 files compile and the axioms are clean. Then hand back. C3 gets a separate brief after a critic check of the defs. It must decide the norm, the substitution lemma and whether E‖Δ̄_T‖² ≤ C/T is already derivable from the `TDInferencePRRemainder711` exports.

D waits for B and C3. G stays deferred and remains the sole blocker for 90/90. The numbered count stays 89/90 throughout.
