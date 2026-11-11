# CRITIC: Theorem 7.11 M4 option (A) — smooth-test-function Gaussian approximation (library infrastructure)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this review covered the builder's pre-integration snapshot. The four modules were integrated unchanged except for their imports and the optional F4 docstring wording, as `Formalization/Analysis/TaylorLipschitzHessian.lean`, `Formalization/Probability/StdGaussianPi.lean`, `Formalization/Probability/LindebergFinite.lean` and `Formalization/TDInference/SmoothApproximation.lean`. Module names below are given under their integrated names; the file hashes and line counts quoted below are those of the reviewed snapshot. The main export is a partial result, not a restricted variant of Theorem 7.11, and it is not counted in the named-result ledger; Theorem 7.11 (corrected) remains open. The review text below is otherwise unchanged.

Date: 2026-11-08. Critic: independent (did not build). No edits to builder files, `Formalization/`, or
`Formalization.lean`; no lake / lean-lsp; no paper fetch. Probes: kept in the reviewer's private probe folder.

## Verdict: **ACCEPT** (no required fixes; optional F-items below; integration conditions I1–I3)

## 0. Target identity (verified)

The builder's reviewed M4 snapshot = the builder's snapshot hash list = the builder's live M4 working files:

| File | sha256 | lines |
|---|---|---|
| TaylorLipschitzHessian.lean | `68eb568d74e065df12e448eef6ed0b88aa0dd859af23d534628b55c309fe087b` | 156 |
| StdGaussianPi.lean | `31f8b404fbb0db7cf47253b07b96462da5b4b0824ac484eb487ca5e390464d85` | 297 |
| LindebergFinite.lean | `7aa3452a7154ed67e381e77b618dca87b397c7e7003b5611293426380196075d` | 453 |
| TDInferenceSmooth711.lean | `81c28c0f98b27d2e817d9a9cce2f6ef482851b1c713083d6f326b39f30ae847e` | 344 |

`git status`: nothing under `Formalization/` or `Formalization/Statements/` changed by M4 (R1 respected).

## 1. Compilation and axioms (independent rebuild)

- Copied the snapshot to a reviewer copy in `<reviewer probe folder>`, changing only the import prefix
  (builder's working prefix → reviewer's private prefix) (StdGaussianPi and Taylor files byte-identical; the other two differ only in
  the import line). Compiled one at a time with
  `bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean <file>`:
  Taylor 9 s, StdGaussianPi 13 s, LindebergFinite 11 s, TDInferenceSmooth711 13 s — all exit 0, **zero
  messages** (no warnings, no `sorry`).
- `CriticProbe.lean` (exit 0): `#print axioms` for all 21 listed exports, including the four key ones
  (`abs_taylor_two_le_of_lipschitz_fderiv_fderiv`, `stdGaussianPi_prod_map_add`, `lindeberg_iid`,
  `scaledError_smooth_gaussian_le`): 21/21 depend only on `[propext, Classical.choice, Quot.sound]`. The main
  export's closure covers the unlisted helpers (`tdY`, `sum_tupleProb_mul_tdY`, `norm_tdY_le`, …).
- Token scan of the snapshot (`sorry|admit|axiom|opaque|implemented_by|native_decide|maxHeartbeats|unsafe|
  set_option|instance|@[simp]`): none in code (one hit is the English word "instance" in a docstring); one
  `private` (`sum_fin_succ_snoc'`, see F1).

## 2. Meaning and junk-freedom

**Taylor** (`abs_taylor_two_le_of_lipschitz_fderiv_fderiv`, any real normed `E`): hypothesis is `ContDiff ℝ 2 f`
and `‖fderiv ℝ (fderiv ℝ f) x − fderiv ℝ (fderiv ℝ f) y‖ ≤ L₂‖x − y‖` (operator norm of the bilinear map);
conclusion `|f(u+h) − f u − Df u h − ½ D²f u h h| ≤ L₂/6 ‖h‖³`. Correct statement, correct (sharp) constant; the
`B(h,h)` form needs no symmetry. Proof by two `image_norm_le_of_norm_deriv_right_le_deriv_boundary` fences — sound.

**stdGaussianPi**: `abbrev = Measure.pi fun _ ↦ gaussianReal 0 1`. Probe P1:
`gaussCov A Γ = (stdGaussianPi S).map (gaussMap A Γ) := rfl` compiles — it is the measure `gaussCov` uses.
Moments `∫zᵢ = 0`, `∫zᵢzⱼ = δᵢⱼ`, `∫(Lz)ᵢ(Lz)ⱼ = (LLᵀ)ᵢⱼ` each come with integrability lemmas; third moment
`E|z|³ ≤ 12e^{1/2}` (true value 2√(2/π) ≈ 1.60, bound ≈ 19.8: loose, correct) and `∫‖z‖³ ≤ |ι|·12e^{1/2}`
(sup norm, via `‖z‖³ ≤ Σ|zᵢ|³`; O1 applied). Stability `aZ + bZ' =ᵈ √(a²+b²)Z` for all real `a, b`
(`a = b = 0` gives `gaussianReal 0 0 = δ₀` through the NNReal variance, no special case). The integral form
`integral_stdGaussianPi_prod_add` **concludes** product integrability from integrability of the target, so the
Fubini step in `abs_sum_integral_sub_integral_le` uses no junk integral.

**Integrability (junk audit).** Every Bochner integral of `f` in a hypothesis or conclusion is of
`f(U + Lz)` with `‖Df‖ ≤ L₁`, proved integrable by `integrable_comp_add_mulVec_stdGaussianPi` (linear growth). No
hypothesis contains an integral. Probe P2 `probe_integrable_gaussCov`: under the export's hypotheses,
`Integrable f (gaussCov (tdA M π μ) (trueGamma M π μ))` — compiles, for **any** `μ` (even without full support), so
the right side of the main export is never the junk 0. `integral_gaussCov_eq` is an identity of integrals that
holds with or without integrability (both sides are pushforward integrals) — correctly documented.

**lindeberg_iid**: hypotheses `p ≥ 0`, `Σp = 1`, `Σₓ p x Y x i = 0` (mean zero) and
`Σₓ p x Y x i Y x j = (LLᵀ)ᵢⱼ` (with mean zero: covariance `LLᵀ`); scaling `(√T)⁻¹ • Σₜ Y(ωₜ)` under product
weights `∏ₜ p(ωₜ)`; bound `L₂/6 (Σ p‖Y‖³ + ∫‖Lz‖³)/√T`, `T > 0`. This is the standard i.i.d. Lindeberg bound with
the right constant (T steps × (L₂/6)T^{-3/2}M). Satisfiable: the TD instance itself discharges the hypotheses
(`sum_tupleProb_mul_tdY`, `sum_tupleProb_mul_tdY_mul`), and probe P3 instantiates the whole chain. Negative `L₂`
is consistent with `hL₂` only when `ι` is empty, where both sides are 0.

**scaledError_smooth_gaussian_le** (printed signature in the builder's axiom probe output re-checked):
- Left: `Σ_{ω : Fin T → Tuple} pathWeight M π μ ω · f(scaledError M π η₀ V₀ ω)` = `E f(√T Δ̄_T)` under the
  i.i.d. path law of the M1 definitions (`pathWeight = ∏ₜ tupleProb`, `tupleProb = μ(s)π(a|s)P(s'|s,a)`,
  `scaledError = √T(prAverage − V^π)`). Correct object.
- Right: `∫ f d gaussCov(tdA, trueGamma)` = `E f(A⁻¹ diag(√Γ_true) Z)` = `∫ f dN(0, A⁻¹ diag(Γ_true) A⁻ᵀ)`;
  `trueGamma s = μ(s)E[ξ² | s]`, the diagonal of the noise covariance (`sum_tupleProb_mul_noiseVec_mul`). `A⁻¹`
  genuine under `0 < μmin ≤ μ(s)`. Correct object (C43 Γ_true).
- Constants: `K = |S|²K_R/((1−γ)μmin)` (per-state M3 bound `|S|K_R/a·T^{-1/6}` summed over `S` states, with
  `‖·‖_∞ ≤ Σ|·|` and Cauchy–Schwarz) and `C = ((B/a)³ + |S|·12e^{1/2}(√maxΓ_true/a)³)/6`. Both are real-valued
  closed forms, finite for `μmin > 0`, `η₀ > 0`; fixed before `T, f, L₁, L₂`; checked line by line against the
  proof (`hsum`, `hm3`). `0 ≤ L₁` and `0 ≤ L₂` are derived from the hypotheses (`[Nonempty State]`), not assumed.
  `rpow` evaluated only at `T ≥ 1`.
- No `Γ ≻ 0` hypothesis; no hidden hypotheses.
- **Non-vacuity (P3, compiles):** instance Z (`zMDP, zPolicy, zMu`, `η₀ = 1/8`, `μmin = 1/2`), arbitrary `V₀`,
  `f x = x 0` (`L₁ = 1`, `L₂ = 0`): the export yields `|E[√TΔ̄_T(0)] − ∫ x 0 dgaussCov| ≤ K T^{-1/6}`.
- **Degenerate case (P4, compiles):** `probe_trueGamma_zero` proves `trueGamma = 0` at instance Z, and
  `probe_degenerate_integral` proves `∫ f d gaussCov(tdA, trueGamma) = f 0` for measurable `f` — the Gaussian is
  `δ₀` and the right side is the genuine `f 0`, not a junk 0. With `V₀ = V^π` the left side is `f 0`
  (`scaledError_zero`), so the bound is consistent; with other `V₀` it is the non-trivial transient statement.

## 3. Docstring compliance (R1–R4)

- **R1**: module and theorem docstrings say "Partial result, not a restricted variant of Theorem 7.11, not counted
  in the named-result ledger". No `_restricted` name, no Statements entry, no ledger change. ✓
- **R2**: "`T^{-1/6}` is the limit of this proof route …; it is not claimed to be the order of the distance itself
  (paper-level heuristics suggest `O(T^{-1/3})`; nothing about that, or about a lower bound, is proved here)". No
  optimality claim. ✓
- **R3**: plan-only; not applicable to this code.
- **R4**: "does **not** imply the printed Theorem 7.11, any convex-set or confidence-region statement
  (`inference.tex:150–200`), or (in Lean) the classic CLT `eqn:classic-clt`"; V₀ dependence through `K`;
  polynomial in `1/((1−γ)μmin η₀)`; "the asymptotic regime may start late". ✓
- Four differences (metric, covariance, rate, no Γ ≻ 0) listed. Source locators checked against
  `source/upstream/tex/chapters/inference.tex`: tuples :52–66, update :70–75, PR average/`Δ̄_T` :80–89, Λ⋆/A/Γ
  :104–117, theorem :132–141 (printed `0 < η₀ < 1/4` at :133, so "printed range included" in `0 < η₀ ≤ 1` is
  right). ✓

## 4. Library quality

- Placement (Analysis/Taylor, Probability/StdGaussianPi + LindebergFinite, Ch7Rest/TDInferenceSmooth711) and
  generality (Taylor for any real normed `E`; Lindeberg for any finite `X`, `ι`, any `L`) are good. Names follow
  Mathlib style.
- `sum_fin_succ_snoc'` private copy: **acceptable**. The shared lemma `StatisticalRL.Fintype.sum_fin_succ_snoc`
  lives in `Ch7Rest/TDInferencePathMarginals711.lean`; importing it into `Probability/` would invert the layering.
  See F1.
- Overlap: `GaussianAntiConcentration.stdGaussianPi_abs_linear_le` uses the literal `Measure.pi …`, reducibly
  equal to the new abbrev — no clash, compatible. `WeightedL2` is reused (`sum_mul_mul_le_weightedL2`,
  `weightedL2_abs`), not duplicated.

## Required fixes

None.

## Integration conditions (lead)

- I1. Move the files byte-for-byte except the module prefix (builder's working prefix → `Formalization.Analysis.` /
  `Formalization.Probability.`), add imports to `Formalization.lean`, recompile and rerun `Audit.lean`.
- I2. COVERAGE/PROGRESS text exactly as in R1 ("partial result, not a restricted variant, not counted"; ledger
  stays 89/90). Also note that the new export does not need Γ_true ≻ 0, whereas the COVERAGE row's corrected
  statement assumes it.
- I3. Before the module goes into `Formalization.lean`, check that no existing file opens both
  `StatisticalRL.Probability` and `StatisticalRL.Ch7Rest.TDInference` and uses the bare name
  `abs_apply_le_norm` (see F2). Builds succeeded here, but it is cheap to check.

## Optional F-items

- F1. Move `StatisticalRL.Fintype.sum_fin_succ_snoc` to a generic module (for example a small
  `Formalization/Probability/FinSnoc.lean` or the Lindeberg file). Then have `TDInferencePathMarginals711` and
  `LindebergFinite` both use it, and drop the private copy.
- F2. Generic helpers in namespace `StatisticalRL.Probability`:
  - `abs_apply_le_norm` is a third copy (also in `Ch7Rest.TDInference` and `VPOGrid712`); it equals
    `norm_le_pi_norm` + `Real.norm_eq_abs`.
  - `mulVec_smul_eq_smul_mulVec` is equivalent to Mathlib `Matrix.mulVec_smul` / `Matrix.smul_mulVec_assoc`.
  - `continuous_mulVec`, `pow_le_one_add_pow_three` and `norm_pow_three_le_sum` are fine but could be `private`
    or moved to Analysis.
  - `matrixAbsSum` is a crude (but correct) operator-norm bound.
- F3. `abs_sum_mul_sub_sum_mul_le_weightedL2` is generic (any finite Ω and weights). It could move to
  `Probability/WeightedL2.lean`, with the codomain generalised from `State → ℝ` to any `ι → ℝ`.
- F4. The theorem docstring's "M4 option A" is internal milestone jargon in a public docstring (earlier M-files do
  the same; consistent, cosmetic).
- F5. P5 (charFun / cos–sin non-vacuity corollary) and O3 (bounded-Hessian lemma `‖D²f‖ ≤ 2√(2L₁L₂)`) remain
  open; D′ will need O3.

## Probe files (kept in the reviewer's private probe folder)

| File | sha256 |
|---|---|
| `CriticProbe.lean` | `0f56d1070696349c0d070619d7a97cf967cf628c71d5d2ccd79bed33a5031c4b` |
| `CriticProbe.out` | `6d5a6c0e816f14bd65d2a65fc63351a2d6f5e55aa7110093c30a9444de668e68` |
| reviewer copy of `LindebergFinite.lean` (import-prefix copy) | `45d35fce72eb8cc057e7756bbbc5cbae1d45066fa3b048e48bb678fb5fd4470e` |
| reviewer copy of `TDInferenceSmooth711.lean` (import-prefix copy) | `f0ca447ceac42065263324476f3b9402b085e921768b20251f60d6f40f43e76d` |
| reviewer copies of `TaylorLipschitzHessian.lean`, `StdGaussianPi.lean` | identical to the snapshot |

Critic oleans were written only under a reviewer-private build folder; they are transient and can be
deleted by the lead.
