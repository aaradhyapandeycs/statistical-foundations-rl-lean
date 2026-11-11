# Critic report: Theorem 7.11 milestone M3 (linear-SA L² theory for PR-averaged TD)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this review (both the first review and the delta review) covered the builder's pre-integration snapshots. The builder applied R1–R3 and F2–F5, F7 before the delta review, and the delta review's docstring fixes D-R1 and D-R2 were applied at integration. The milestone modules were integrated as `Formalization/Probability/WeightedL2.lean`, `Formalization/Analysis/StepSizeCubeRoot.lean`, `Formalization/TDInference/StepSize.lean`, `Formalization/TDInference/Noise.lean`, `Formalization/TDInference/Martingale.lean`, `Formalization/TDInference/Operator.lean`, `Formalization/TDInference/PolyakRuppert.lean` and `Formalization/TDInference/PolyakRuppertRemainder.lean`; the first snapshot's step-size schedule module was split (per R3) into `StepSizeCubeRoot.lean` and `TDInferenceStepSize711.lean`. Module names below are given under their integrated names; the file hashes and line numbers quoted below are those of the reviewed snapshots. This milestone is infrastructure toward a corrected Theorem 7.11, which remains open: no corrected Theorem 7.11 is proved, and no statement-index entry suggests one. The review text below is otherwise unchanged.

Date: 2026-11-08. Critic: independent (did not build M3). Scope: library infrastructure for the C43-corrected
Thm 7.11 (`thm:Berry-Esseen-linear`, `source/upstream/tex/chapters/inference.tex:50–200`); not a source theorem.

## Verdict: ACCEPT WITH FIXES

The mathematics is sound and every key export means what it says, for the actual M1 objects (`tdIter`,
`pathWeight`, `stepSize`, `tdA`, `trueGamma`, `scaledError`). No junk-value loopholes found. The required fixes are
docstring accuracy and module placement before integration into `Formalization/`. None changes a theorem statement.

## Evidence

- The builder's first M3 snapshot (7 files, 1755 lines). The sha256 values match the builder's snapshot hash list.
  The builder's live M3 working files are byte-identical to the snapshot (checked with `cmp`).
- Token scan on the snapshot finds no `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `implemented_by` or `unsafe`.
- Independent recompile of every snapshot module. Each was run with `bash scripts/lean-local.sh <file>`, foreground,
  one at a time, against the existing M1/M2/M3 oleans. All seven exit 0 with 0 warnings and 0 errors. Log:
  `<reviewer probe folder>/snapshot-recompile.out`. The builder's snapshot oleans postdate the
  sources, and the hashes in the builder's build log (entries #31–#42) equal the snapshot hashes.
- Critic probe `<reviewer probe folder>/CriticProbeM3.lean` (sha256 `0dc43ea9…a7c86`) exits 0. Output:
  `critic-probe-m3.out` (sha256 `53fadd29…1f686`). It covers the following.
  - `#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]` for:
    - `tdSecondMoment_le`
    - `weightedL2_scaledError_sub_prGaussPart_le_rpow` and `weightedL2_scaledError_sub_prGaussPart_le`
    - `sum_pathWeight_mul_sq_prNoiseSum`
    - `tdA_isUnit`
    - `scaledError_sub_prGaussPart`
    - `prResidual_apply`
    - `trueGamma_eq`
    - `tupleCondExp_tdNoise`
    - `sum_pathWeight_mul_sq_sum_eq`
    - `sum_pathWeight_mul_sq_prMartingale_le`
    - `norm_tdA_inv_mulVec_le`

    The builder's axiom probe output (99 declarations) also shows only these three. Note that the builder's probe (build-log entry #40) predates rebuild
    #41 of TDInferencePolyakRuppert711; my probe re-checks against the final oleans.
  - (P1) `weightedL2 (pathWeight M π μ) f ^ 2 = E f²`. The seminorm is the genuine L² norm of the path law, not
    something that can vanish trivially.
  - (P2) The hypotheses are satisfiable: any full-support μ has some `μmin > 0` with `μmin ≤ μ(s)` for all `s`.
  - (P3) Non-vacuity of the rate theorem. Under its hypotheses, `‖(√TΔ̄_T − W_T)(s)‖_{L²(path law)} → 0` as
    `T → ∞`, derived from `weightedL2_scaledError_sub_prGaussPart_le_rpow`.
  - (P4) The noise sum is centred on the path law: `E (∑_k ξ_k)(s) = 0` for every `T` (proved in about 10 lines).

## Statement-meaning checks (item 2)

- **`tdNoise` and `Γ_true`.** `tdNoise M π (s,a,s') = V^π(s) − r(s,a) − γV^π(s')`. This is exactly the integrand of
  M1's `trueGamma`, and `trueGamma_eq` is `rfl`, which matches the C43 formula. The noise uses the per-action reward
  `r(s,a)`, not `r_π(s)`, as C43 requires.
- **`E[ξ|s] = 0` (`tupleCondExp_tdNoise`).** It is proved from `M.valueFixedPoint_spec π`, the Bellman equation of
  the actual `V^π`, through `tupleCondExp_affine`. The conditional law is `π(·|s) ⊗ P(·|s,a)`, matching `tupleProb`.
  `sum_tupleProb_mul_ite_zero` gives `E[1{s₀=s} g] = μ(s) E[g|s]` correctly.
- **`tdSecondMoment_le`.** The bound is stated for M1's `tdIter` on M1's `pathWeight`.
  - `tdSecondMoment t s` sums over `Fin t → Tuple`. The bridge to the horizon-T law is the M2 marginal lemma
    `sum_pathWeight_mul_tdIter_of_le`, used in `weightedL2_tdError_eq`.
  - Hypotheses: `0 < η₀ ≤ 1`, `0 < μmin`, `∀ s, μmin ≤ μ(s)`, `t ≥ 1`.
  - Division safety:
    - `μmin(1−γ) > 0` by hypothesis plus the structural `discount_lt_one`, so the case γ = 1 cannot occur.
    - `stepSize η₀ t₁ > 0` because `t₁ ≥ 1` and `η₀ > 0`.
    - There are no rpow terms at base 0 for `t ≥ 1`.
  - Constant: `C = max(2(B²+2BD)/(μmin(1−γ)), D²/η_{t₁})` with `t₁ = ⌈(2/(μmin(1−γ)η₀))³⌉ + 1`.
    - In the induction, the burn-in phase uses the pathwise bound `D²`.
    - After the burn-in, the slow-variation condition `2/(aη₀) ≤ (t+1)^{1/3}` is derived from `t₁`. The induction is
      sound.
    - Scaling: `C ≍ D²/(η₀³μmin²(1−γ)²)`. This is polynomial, as disclosed.
- **Pathwise bound.** `|V_t − V^π| ≤ D = max(‖V₀−V^π‖_∞, B/(1−γ))` holds for every path and every `t` (frozen indices
  included), with `B = 1 + (1+γ)‖V^π‖_∞`. It uses `r ∈ [0,1]`. This is correct and the reason the route works.
- **PR decomposition.**
  - `prResidual_apply` is an exact pathwise identity for all `T` (including `T = 0`).
  - The summation-by-parts weights are `w_k = invStepSize η₀ k`, with `w_0 = 0` handled correctly.
  - Index alignment: the sample `ω k` drives `V_k → V_{k+1}`, consistent with M1's `tdIter`. The martingale term is
    `f k (V_k) (ω k)`, which is correct.
  - `scaledError_sub_prGaussPart` (with `T ≥ 1`, `μmin > 0`) uses the genuine inverse through `tdA_isUnit`, which
    follows from strict diagonal dominance (`(1−γ)μmin‖v‖ ≤ ‖Av‖`).
- **Remainder bounds.**
  - `‖R_T(s)‖_{L²}` is bounded by `√(4D² + 12Cη₀u_T) + 4√C u_T/√η₀ + D/η₀ + 4D`, where `u_T = T^{1/3}`.
  - The `4D²` term is the `k = 0` martingale increment, where only the pathwise bound applies.
  - The telescoping and endpoint terms contribute `4√C u_T/√η₀`.
  - Then `‖·‖_∞ ≤ ∑_s |·|` gives the factor `S`, and `‖A⁻¹‖_{∞} ≤ 1/((1−γ)μmin)`.
  - `prResidualBound_le` uses `√(a + b u) ≤ √a + √b·u` for `u ≥ 1`. `cubeRoot T/√T = T^{-1/6}` is checked.
  - `prRemainderConst = 2D + √(12Cη₀) + 4√C/√η₀ + D/η₀ + 4D` matches its docstring and the module header.
- **Covariance identity (`sum_pathWeight_mul_sq_prNoiseSum`).** It holds for every `T` (`T = 0` gives `0 = 0`) and
  every `c`.
  - Independence across `k` comes from the product law, via `pathWeight_snoc` inside the martingale-orthogonality
    induction `sum_pathWeight_mul_sq_sum_eq`, applied with a `V`-independent increment.
  - The per-sample identity `E_x ξ_x(s)ξ_x(s') = 1{s=s'}Γ_true(s)` is correct, because `ξ_x` is supported on the
    coordinate `x.1`.

## Caveat accuracy (item 3)

The builder's status-note and module-docstring caveats are accurate:
- The rate is `T^{-1/6}`, not `T^{-1/3}`.
- `K_R` depends on `D` (through `‖V₀−V^π‖_∞`), on `B` (through `‖V^π‖_∞`) and on the burn-in, which is polynomial in
  `1/(μmin(1−γ)η₀)`.
- There is an extra `|State|` factor.
- The bound is not on the `Tr Γ_true` scale, so the homogeneity of the plan check (docs/critic-thm7-11-plan-check.md) §4.2 and F6 is not reflected.
- The covariance limit `Cov(√TΔ̄_T) → A⁻¹Γ_trueA⁻ᵀ` is not stated.
- The route change away from the builder's private plan M3(a)–(c) is disclosed.

The only over-claims are in docstrings (R1, R2).

## Required before integration (R-items)

- **R1 (docstring references to nonexistent names).**
  - `TDInferencePolyakRuppert711.lean:26` cites `sum_pathWeight_mul_prNoiseSum_mul`, which does not exist. The export
    is `sum_pathWeight_mul_sq_prNoiseSum`, a quadratic-form identity, not the cross-moment form quoted.
  - `TDInferenceNoise711.lean:24,26` cite `secondMoment_succ_le` and `secondMoment_le`. The actual names are
    `tdSecondMoment_succ_le` and `tdSecondMoment_le`.
  - Fix the names, or prove the quoted cross-moment lemma.
- **R2 ("Cov(W_T) = A⁻¹ diag(Γ_true) A⁻ᵀ exactly" is not a Lean statement).** This appears in the TDInferencePolyakRuppert711
  header (:26–27) and in the docstring of `sum_pathWeight_mul_sq_prNoiseSum`.
  - It is true: probe P4 proves centredness, and polarization of the quadratic identity gives the cross terms.
  - However, no export states it, and centredness is not exported.
  - Fix: either add the two short lemmas (centredness of `prNoiseSum`; the cross-moment by polarization), or reword to
    "implies (informally, not stated here) …".
- **R3 (placement before moving to `Formalization/`).**
  - (a) The snapshot's step-size schedule module cannot go to `Formalization/Analysis` as is: it imports `TDInference711Defs` for
    `stepSize` and lives in `StatisticalRL.Ch7Rest.TDInference`. Split it:
    - The generic cube-root facts move to `Formalization/Analysis/StepSizeSums.lean`, or a sibling in its namespace
      `StatisticalRL.Probability`. These are `cubeRoot*`, `sq_sub_sq_le_inv_of_cube_sub_eq_one`,
      `inv_sq_le_three_mul_sub_of_cube_sub_eq_one` and `rpow_two_thirds_eq`.
    - The `stepSize` and `invStepSize` lemmas stay in `Formalization/Ch7Rest/` under a `…711` name.
  - (b) `stepRecursion_le` (Chung step) is a step-size recursion lemma, not an L² fact. Move it out of `WeightedL2.lean`
    into the step-size module.
  - `WeightedL2.lean` itself is generic (`StatisticalRL.Probability`, Mathlib-only imports) and fits
    `Formalization/Probability/WeightedL2.lean` unchanged.

## Optional (F-items)

- **F1 (duplicates).**
  - `prob_le_one` (TDInference namespace) is a third copy, after `DiscountedMDP.finiteDistribution_prob_le_one`
    (`Formalization/MDP/DiscountedOccupancy.lean:47`) and `Ch7Rest.Marl77.prob_le_one`. Reuse one, or promote it to
    `FiniteDistribution.prob_le_one` in core.
  - `sum_mul_sq_sub_mean_le` is the `c = 0` case of `Probability.sum_sq_sub_mean_le`
    (`Formalization/Probability/MixtureVariance.lean:23`). Derive it from that lemma or cross-reference it.
  - `abs_apply_le_norm` is `norm_le_pi_norm` plus `Real.norm_eq_abs`, and the same name exists in `Ch7Rest.Rlhf`.
- **F2.** Remove the literal `+ 0` from the statement of `sum_tupleProb_mul_sq_prMartingaleTerm_le` (:30) and its
  uses.
- **F3.** `prMartingaleTerm` has an unused `_k : ℕ` binder, present only to fit the `f : ℕ → …` shape of
  `sum_pathWeight_mul_sq_sum_eq`. Document this, or adapt with `fun _ ↦`.
- **F4.** The definition docstrings of `prGaussPart` and `prResidual` should say that `(tdA)⁻¹` is `Matrix.inv`, which
  is the junk value 0 when `μ` lacks full support. Every theorem using them assumes `μmin > 0`.
- **F5.** Export the probe facts P3 (`L²` remainder → 0) and P4 (centredness) as library lemmas. M4 and the
  covariance-limit corollary will need them.
- **F6.** About 120 lines exceed 100 characters. Project-wide this is common (about 5k lines), so it is not blocking.
- **F7.** `cubeRoot` is a very generic name in `Ch7Rest.TDInference`. Once moved (R3a), consider a more specific name
  or Mathlib-style `rpow` lemmas.

## Files

- Report: the private original of this public copy.
- Probes and logs (kept in the reviewer's private probe folder):
  - `CriticProbeM3.lean`
  - `critic-probe-m3.out`
  - `snapshot-recompile.out`
- No builder files, `Formalization/` files or `Formalization*` oleans were touched. No olean was written by the
  critic.

---

## Delta review (second snapshot, 2026-11-08)

### Verdict: ACCEPT WITH FIXES (two docstring fixes, no statement changes)

### Evidence
- The builder's second M3 snapshot has 8 modules.
  - The sha256 values match the builder's second snapshot hash list.
  - The builder's live M3 working files are byte-identical to the snapshot.
  - The old step-size schedule module and its olean are gone. No module imports it.
- The token scan on the snapshot is clean.
- Each second-snapshot module was recompiled with `bash scripts/lean-local.sh <file>`, foreground, one at a time, with no
  olean written. All 8 exit 0 with 0 warnings and 0 errors. Log:
  `<reviewer probe folder>/snapshot2-recompile.out`.
- Probe `<reviewer probe folder>/CriticProbeM3Delta.lean` (sha256 `9fb6459a…a096`) exits 0. Output:
  `critic-probe-m3-delta.out` (sha256 `fd786cbd…3587`).
  - `#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]` for:
    - the 7 new lemmas;
    - `sum_tupleProb_mul_sq_prMartingaleTerm_le`;
    - `stepRecursion_le`;
    - `sum_range_inv_sq_natCubeRoot_succ_le`;
    - `natCubeRoot_div_sqrt_eq`;
    - `tdSecondMoment_le`;
    - `weightedL2_scaledError_sub_prGaussPart_le_rpow`.
  - (D1) Junk check. If `det A` is not a unit, `prGaussPart M π μ ω = 0` for every path.
  - (D2) Under `0 < μmin ≤ μ(s)`, `(tdA)⁻¹ * tdA = 1`.
  - (D3) `natCubeRoot t = (t:ℝ)^(1/3)` holds by `rfl`.

### (1) R1–R3
- **R1: resolved.**
  - The `TDInferenceNoise711.lean` header now cites `tdSecondMoment_succ_le` and `tdSecondMoment_le`.
  - The `TDInferencePolyakRuppert711.lean` header cites only declarations that exist.
  - New, same class: the `StepSizeCubeRoot.lean:14` header cites `natCast_natCast_rpow_two_thirds_eq`, which does not
    exist. The real name is `natCast_rpow_two_thirds_eq`. This is a rename artifact. See **D-R1**.
- **R2: resolved.** The Cov claim is now backed by actual exports: centredness, the bilinear form, the cross-moment and
  `E W_T W_T'`.
- **R3: resolved.**
  - `StepSizeCubeRoot.lean` imports Mathlib only and uses namespace `StatisticalRL.Probability`. It contains the
    cube-root lemmas and `stepRecursion_le`.
  - `TDInferenceStepSize711.lean` (Ch7Rest) contains the `stepSize`/`invStepSize` lemmas.
  - `WeightedL2.lean` no longer contains `stepRecursion_le`.

### (2) New lemma statements
- **`sum_pathWeight_mul_prNoiseSum`:** `E N(s) = 0` for every `T` and `s`.
  - It has no hypotheses and needs none, because `E_x ξ_x(s) = 0` follows from Bellman alone.
  - It is the same proof as my probe P4.
- **`sum_pathWeight_mul_sum_prNoiseSum_mul`:** `E[(c·N)(d·N)] = T ∑ c_s d_s Γ_true(s)`.
  - It is derived by polarization from the quadratic identity, for every `T`, `c` and `d`.
- **`sum_pathWeight_mul_prNoiseSum_mul`:** `E N(s)N(s') = T·[s=s']Γ_true(s)`.
  - It is obtained with `c = e_s` and `d = e_{s'}`.
- **`prGaussPart_apply`:** this unfolds the definition, nothing more.
- **`sum_pathWeight_mul_prGaussPart`:** `E W_T(s) = 0`. It is unconditional and true for any matrix.
- **`sum_pathWeight_mul_prGaussPart_mul`:** for `T ≥ 1`, `E W_T(s)W_T(s') = (A⁻¹ diag Γ_true A⁻ᵀ)(s,s')`.
  - Since `E W_T = 0`, this is indeed the covariance.
  - `T ≥ 1` is needed: at `T = 0`, `W_T = 0` while the right-hand side need not be 0. The hypothesis is present.
  - Junk: there is **no** full-support hypothesis.
    - `A⁻¹` is `Matrix.inv` on both sides, so the identity is true unconditionally.
    - When `A` is singular, both sides collapse to the junk value 0 (probe D1), so the identity says nothing about TD.
    - Under `0 < μmin ≤ μ(s)`, `A⁻¹` is the genuine inverse (D2) and the statement has its intended meaning.
  - The docstring says only "with `A⁻¹ = Matrix.inv (tdA M π μ)`". It must say that this is the genuine inverse only
    under full support, and the junk value 0 otherwise. See **D-R2**.
  - The `prGaussPart` definition docstring (F4) already says this correctly.
- **`tendsto_weightedL2_scaledError_sub_prGaussPart`:**
  - Hypotheses: `0 < η₀ ≤ 1`, `0 < μmin ≤ μ(s)`.
  - Conclusion: L² of `(√TΔ̄_T − W_T)(s)` tends to 0.
  - It is derived from the `T^{-1/6}` rate bound. This is the same statement as my probe P3. Correct and non-vacuous.

### (3) F2 and F7 are meaning-preserving
I diffed the second snapshot against the first.
- **F2:** only `+ 0` was dropped from the statement of `sum_tupleProb_mul_sq_prMartingaleTerm_le`. Its one use adapts
  through `add_zero`.
- **F7:**
  - `cubeRoot` became `natCubeRoot`, with an identical body (D3). `rpow_two_thirds_eq` became
    `natCast_rpow_two_thirds_eq`.
  - `cubeRoot_one` and `cubeRoot_div_sqrt_eq` moved verbatim as `natCubeRoot_one` and `natCubeRoot_div_sqrt_eq`.
  - After undoing the renames, the old step-size schedule module and the new pair (`StepSizeCubeRoot.lean`,
    `TDInferenceStepSize711.lean`) differ only in headers, namespace or imports, and these additions:
    - the moved lemmas;
    - the new `sum_range_inv_sq_natCubeRoot_succ_le`, a correct `η₀`-free form of the old sum bound;
    - the reformatted signature of `stepRecursion_le`, with identical binders.
  - Every `stepSize` lemma statement is unchanged.
- **Other edits:** the TDInferenceNoise711, TDInferencePolyakRuppert711 and WeightedL2 diffs touch only docstrings and imports, apart from the
  rename in the `hcube` proof step. The renamed statements in TDInferencePRRemainder711 (`prResidualBound`, `_le`, telescope,
  endpoint, martingale) have identical meaning.
- **F1 and F3:** F1 remains a disclosed cross-reference, which is acceptable (optional item). F3 is now documented.

### (4) Namespace clash check
- I compared the declaration names in `StepSizeCubeRoot.lean` and `WeightedL2.lean` against every declaration in
  every `Formalization/` file that opens `namespace StatisticalRL.Probability`, including `Analysis/StepSizeSums.lean`.
  There is **no overlap**.
- `natCubeRoot` and `cubeRoot` occur nowhere in `Formalization/`.

### Required (delta)
- **D-R1.** In the `StepSizeCubeRoot.lean:14` header, change `natCast_natCast_rpow_two_thirds_eq` to
  `natCast_rpow_two_thirds_eq`.
- **D-R2.** In the docstring of `sum_pathWeight_mul_prGaussPart_mul`, add that `A⁻¹` is `Matrix.inv`. It is the genuine
  inverse when `0 < μmin ≤ μ(s)` (`tdA_isUnit`); otherwise `A⁻¹` and `W_T` are the junk value 0 and the identity is
  `0 = 0`.

Neither fix touches a statement. Once both are applied, the milestone is ready for integration without further
review; a docstring-only check by the lead is sufficient.
