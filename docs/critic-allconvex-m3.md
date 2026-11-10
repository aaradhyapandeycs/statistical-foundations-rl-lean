# CRITIC — all-convex Thm 7.11 route, milestone M3 (Gaussian IBP + smoothing derivative bounds)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Infrastructure review for the all-convex Theorem 7.11 route, not a source result: no COVERAGE row, statement-index entry or named-result change follows from it. Reviewed: M3 (Gaussian integration by parts and smoothing derivative bounds), `Formalization/Probability/GaussianIBP.lean`. Planning notes cited below (route plan, M5a design and design check, M6a interface note) are local and not published; the route plan check is public as [critic-allconvex-p0.md](critic-allconvex-p0.md). Probes are local scratch files (`<local probe>`).

Critic: independent (not the builder). Date 2026-11-09.
Under review: `Formalization/Probability/GaussianIBP.lean`, 644 lines,
sha256 `58cfab96c93cdcd1c6d1211c09f456e7b820cdbdbf8504c45e5476d5538cedff` (matches builder STATUS).
Critic probe: `<local probe>`, log `<local log>`.

## Verdict: ACCEPT (with minor, non-blocking fixes F1–F3)

No mathematical, hidden-hypothesis or constant-dependence defect found. Infrastructure only, not a source
result; no COVERAGE/Statements entry is due.

## Evidence

- Command: `bash scripts/lean-local.sh <local probe>`
  (imports `Formalization`, `Formalization.Probability.GaussianIBP`, `Formalization.Analysis.ConvexSmoothIndicator`;
  run only when `pgrep -x lean | wc -l` < 2). Exit 0, no errors, no warnings.
- `#print axioms` on all main exports and on the critic's consumer-shaped theorems: only `propext`,
  `Classical.choice`, `Quot.sound`. Builder probe (27/27 decls) also re-read: same.
- grep: no `sorry`, `admit`, `axiom` in the module.
- Name collisions: none of the 27 names is declared elsewhere in `Formalization/` or the builder work-in-progress folders.
  Only a near-duplicate `StatisticalRL.Analysis.ConvexSmoothIndicator.integral_linearIsometryEquiv_comm`
  (different namespace, unprimed) — no clash (F1).
- Not yet imported from `Formalization.lean` (lead integrates).

## Review findings by question

R1. 1-D IBP (`integral_smul_gaussianReal_eq_integral_deriv`). Re-derived: Mathlib
`integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable` with u = stdPDF, u' = −t·stdPDF, v = G gives
∫ pdf·G' = −∫(−t pdf)G = ∫ t pdf G. The three integrability side conditions are discharged from bounded G, G'
times the integrable pdf / t·pdf; continuity of G' is used only for measurability. Boundary terms are handled
inside the Mathlib lemma (integrability ⇒ limits). Correct; hypotheses are the natural ones.
Coordinate Fubini: `map_update_prod_stdGaussianPi` proved by `Measure.pi_eq` on boxes (preimage of a box is
box-with-univ × s i; product of masses). Correct. `integral_stdGaussianPi_eq_integral_update` then
`integral_prod`. The coordinatewise and directional IBP follow by chain rule along `Function.update` and
linearity. Correct.

R2. Derivative moving and induction. One step (`norm_gaussSmooth_fderiv_le`): for h, pick w with Lw = h,
‖w‖₂ ≤ r‖h‖∞; then D(Eψ(x+LZ))·h = E[Dψ(x+LZ)(Lw)] = E[⟨w,Z⟩ψ(x+LZ)] (IBP on g(z)=ψ(x+Lz)),
and E|⟨w,Z⟩| ≤ ‖w‖₂ (proved via 2c|X| ≤ c²+X² and E X² = ‖w‖₂²). Gives r·sup‖ψ‖. Correct.
Induction: `gaussSmooth φ L = gaussSmooth (gaussSmooth φ (aL)) (aL)`, a = 1/√2 (semigroup lemma uses
`stdGaussianPi_prod_map_add` with √(a²+b²) = 1). Dᵏ⁺¹ of the outer smoothing = outer smoothing of D(Dᵏψ);
one-step bound with radius √2·r (preimage √2·w for aL), and C₀ = sup‖Dᵏψ‖ ≤ gdc k (√2 r)ᵏ B by the IH applied
to (aL, √2 r) — the IH is correctly universally quantified over L and r. Total √2 r · gdc k (√2 r)ᵏ B =
√2^{k+1} gdc k · r^{k+1} B = gdc(k+1) r^{k+1} B. Matches the definition. Values checked in probe:
gdc 1 = √2, gdc 3 = 8 (gdc k = 2^{k(k+1)/4}; not sharp, but a fixed constant per k — acceptable).

R3. Right-inverse / quadratic form (`exists_mulVec_eq_of_quadForm_ge`). Hypothesis v‖u‖∞² ≤ uᵀLLᵀu makes LLᵀ
injective hence invertible; a = (LLᵀ)⁻¹h, w = Lᵀa, ‖w‖₂² = aᵀLLᵀa = a·h. Then v‖a‖∞² ≤ a·h ≤ |ι|‖a‖∞‖h‖∞ gives
‖a‖∞ ≤ |ι|‖h‖∞/v and a·h ≤ |ι|²‖h‖∞²/v. So ‖w‖₂ ≤ (|ι|/√v)‖h‖∞. The sup-norm/Euclidean conversion is correct
(Σ aᵢhᵢ ≤ |ι|·‖a‖∞‖h‖∞); it loses √|ι| against the optimal Euclidean route, harmless (ι-only constant).
The sup-norm hypothesis is *weaker* than the Euclidean one used by the M5a design (not published) / M6a (‖u‖∞² ≤ u·u); the
critic proved the implication (`critic_sup_of_euclid`) in the probe.

R4. Constants. Final bound `gaussDerivConst k * card ι ^ k * B * v^(-k/2)`: no ι', no derivative bounds of φ
(the `hbd` / `C₁` hypotheses are existential and only feed differentiability under the integral). ι' is a free
`Fintype` in every statement. Confirmed by `critic_L20_shape` with R : Matrix ι (κ × ι) ℝ, whose bound
`(gaussDerivConst 3 * card ι ^ 3) * (v * √v)⁻¹` does not mention κ.

R5. Adequacy for the M5a design (not published) L20. Yes. L20 smooths the M2 sandwich φ (C^∞, values in [0,1], bounded D⁰…D³)
through the rectangular reservoir R = twinMat L (resSet e k) : Matrix ι (κ×ι) ℝ. The probe instantiates exactly
this with M2 `smoothIndicator` (n = 3, B = 1) and obtains in one theorem: `ContDiff ℝ 3 (gaussSmooth φ R)`,
the k = 3 bound in the `(v*√v)⁻¹` form and the k = 1 bound in the `(√v)⁻¹` form, from the Euclidean hypothesis.
Fallback F-a (square reduction) is unnecessary. Bounded-measurable (non-smooth) φ is not covered; L20 does not
need it.

R6. Hidden hypotheses / non-vacuity. All hypotheses are explicit and natural (ContDiff n, bounded derivatives up
to n, ‖φ‖ ≤ B, v > 0, quadratic-form lower bound, k ≤ n). Non-vacuity: builder probe (L = 1, s·I, IBP on the
M2 indicator) and critic `critic_rect_nonvacuous` (rectangular R = [I | 0] on Fin 2 × ι satisfies the Euclidean
hypothesis with v = 1). The `omit [CompleteSpace F]` on some lemmas is harmless (statements stay true; the
consumers use F = ℝ).

## Fixes (non-blocking)

- F1. `integral_linearIsometryEquiv_comm'` duplicates `LinearIsometry.integral_comp_comm` (and the M2 lemma);
  inline or make `private` to avoid API clutter.
- F2. Possibly unused import `Mathlib.MeasureTheory.Integral.IntegralEqImproper`; check and drop if unused.
- F3. On integration: add the module to `Formalization.lean` (and whatever import gate lists modules) so the
  repository axiom audit covers it; rerun `python3 scripts/check.py`.

## Notes for M5a / M4.2

- Use `hermiteConst ι k := gaussDerivConst k * (Fintype.card ι : ℝ) ^ k` with B = 1. The rpow conversions
  `v ^ (-(3:ℕ:ℝ)/2) = (v * √v)⁻¹` (`Real.sqrt_eq_rpow`, `Real.rpow_one_add'`, `Real.rpow_neg`, `norm_num`) and
  `v ^ (-(1:ℕ:ℝ)/2) = (√v)⁻¹` are in `critic_L20_shape`; copy them.
- Euclidean → sup-norm hypothesis adapter: `critic_sup_of_euclid` (≈15 lines); M5a should own a copy.
- `ContDiff ℝ 3` comes from `contDiff_gaussSmooth` with n = 3; L19 then converts the k = 3 bound to Lipschitz
  Hessian and the k = 1 bound to ‖fderiv‖ (via `norm_iteratedFDeriv_one`/`norm_fderiv_iteratedFDeriv`).
- For M4.2 / mixed bounds: the right-inverse form `norm_iteratedFDeriv_gaussSmooth_le_of_rightInv` is the more
  flexible entry point (any explicit preimage map with Euclidean control).
