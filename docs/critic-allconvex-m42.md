# CRITIC report: M4.2 Gaussian-vs-Gaussian convex comparison (all-convex Thm 7.11 route)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Infrastructure review for the all-convex Theorem 7.11 route, not a source result: no COVERAGE row, statement-index entry or named-result change follows from it. Reviewed: M4.2 (Gaussian-vs-Gaussian convex comparison), `Formalization/Probability/GaussianConvexCompare.lean`. Planning notes cited below (route plan, M5a design and design check, M6a interface note) are local and not published; the route plan check is public as [critic-allconvex-p0.md](critic-allconvex-p0.md). Probes are local scratch files (`<local probe>`).

Reviewed file: Formalization/Probability/GaussianConvexCompare.lean (618 lines,
sha256 387b349c1120e936293b0d744fb98024f955c1484654bc6e387f1f09c9279ac8, same hash as the builder's status note).
Critic artifacts: local module log, probe and probe log (not published).

## Verdict: ACCEPT (with two integration fixes and optional cleanups)

## Evidence (critic-run, one Lean process at a time, pgrep count 0 before each)
- `bash scripts/lean-local.sh Formalization/Probability/GaussianConvexCompare.lean` -> exit 0, no output
  (no errors, no warnings), 23.7 s wall.
- `bash scripts/lean-local.sh <local probe>` (imports Formalization +
  the module together: no name clashes) -> exit 0. `#print axioms` for abs_real_convex_gaussian_sub_le,
  abs_real_convex_gaussCov_sub_le, abs_integral_map_sub_le_of_contDiff, abs_gaussSmooth_sub_le,
  real_le_integral_le_add_shell, exists_square_factor_isUnit, posSemidef_smul_one_sub,
  posSemidef_gram_sub_reservoir: all exactly [propext, Classical.choice, Quot.sound].
- grep: no sorry / admit / axiom / set_option in the file. No repo-wide declaration-name collisions for the 21
  new names checked.
- Probe additions (all compile): (a) Euclidean lambda_min hypothesis => the sup-norm hypothesis (one-line bridge);
  (b) a 2-D family N((1+t)I) vs N(I), v = 1, every convex K, instantiating the main theorem (hypotheses satisfiable,
  non-vacuous); (c) entryMax on an empty index type is 0.

## Reconstruction of the mathematics (independent)
(1) Reservoir split. n = |ι|, r = v/(n+1). For x: r·Σx_i² ≤ r·n·‖x‖∞² ≤ v‖x‖∞² ≤ xᵀΣx, so Σ − rI ⪰ 0.
    The sup-vs-Euclidean issue is handled correctly (factor n; n+1 only to cover n = 0). Hypothesis in sup norm is
    WEAKER than the Euclidean λ_min form, so the theorem is stronger, not weaker. N(Σ) = law of [P | √r I] Z via
    M4.1 law identity (map_mulVec_stdGaussianPi_eq) and Fubini through measurePreserving_sumPiEquivProdPi_symm:
    checked in integral_map_fromCols_mulVec / abs_integral_map_sub_integral_fromCols_le.
(2) Common upper covariance. δ = Σ₁ − Σ₂ symmetric; xᵀδx ≤ m(Σ|x_i|)² ≤ m·n·Σx_i² (Cauchy–Schwarz), m = entryMax δ,
    so ‖δ‖₂ ≤ n·m and D₁ = cI − δ ⪰ 0 with c = n·m; D₂ = cI ⪰ 0. P₁P₁ᵀ + D₁ = Σ₂ − rI + cI = P₂P₂ᵀ + D₂: same law.
    Taylor: |h(y+w) − h(y) − Dh(y)w| ≤ M‖w‖∞² ≤ M Σw_i² (M bounds the sup-norm operator norm of D²h; the true
    constant is M/2, so the file is loose by 2, harmless). First-order term integrates to 0 because each coordinate
    of QZ is integrable with mean 0 (linear functional expanded in coordinates). E Σ(QZ)_i² = tr(QQᵀ). Correct.
    tr D₁ ≤ n(c+m), tr D₂ = nc.
(3) Constant: M = gaussDerivConst 2 · n / r (from M3 with B = 1, s = √r; only sup|φ| ≤ 1 enters, ε-free).
    Total = M·n(2c+m) = G·n(n+1)/v · n(2n+1)·m = gaussCmpConst ι / v · m. Matches the definition exactly; no ε, no
    √ rate, linear in entryMax δ. gaussDerivConst 2 = 2√2 (concrete).
(4) ε → 0: real K = real (interior K) for arbitrary (non-measurable) convex K under a nondegenerate Gaussian (M1
    map_mulVec_real_convex_eq_interior, via square invertible factor R from exists_square_factor_isUnit, which
    correctly derives injectivity of LLᵀ from the v-hypothesis). φ = upper smooth sandwich of interior K (M2):
    real K ≤ ∫φ ≤ real(thickening ε U) ≤ real U + shell ≤ real K + C_i ε, C_i = 4n²‖R_i⁻¹‖_rowsum/√(2π), fixed
    before ε is chosen. Then |Δ| ≤ A + (C₁+C₂)ε for all ε > 0 and le_of_forall_pos_le_add. Sound.
(5) Hypotheses: only 0 < v and the two lower bounds, plus convexity of K. No measurability, no hidden smoothness.
    gaussCov corollary: if A is singular, A⁻¹ = 0 makes the hypotheses unsatisfiable (v > 0), so no junk-value issue.

## Findings
- F1 (integration, required before landing): module is not imported from Formalization.lean, so the repo axiom audit
  does not cover it. Lead adds `import Formalization.Probability.GaussianConvexCompare` (after GaussianCovCompare,
  line ~937) and to any gate import list (scripts/gates/g2_statement_imports.txt only if statement files import it).
- F2 (integration, required): record ownership/status in docs/PROGRESS.md as infrastructure (not a source result);
  do NOT mark Theorem 7.11 or any source label proved on the strength of this module.
- R1 (optional): generic helper names inside namespace GaussianConvexCompare (transpose_mul_transpose_self,
  posSemidef_of_dotProduct, norm_sq_le_sum_mul_self, isHermitian_of_transpose_eq) may become ambiguous if a consumer
  opens both this namespace and Matrix; consider `private` or more specific names. No current clash.
- R2 (optional): export the Euclidean-to-sup-norm bridge (probe example (a)) next to the main theorem, since
  consumers usually have λ_min in Euclidean form.
- R3 (cosmetic): Taylor remainder uses M instead of M/2; the constant could be halved. Not a correctness issue.

## Notes for M6.3 / M7 consumers
- BOTH covariances need the lower bound v‖u‖∞² ≤ uᵀΣᵢu. If one side is a plug-in / finite-sample covariance,
  its lower bound must be established (e.g. from Σ_true ⪰ v₀ and entryMax(Σ̂ − Σ) ≤ v₀/(2n) giving v = v₀/2);
  do not assume it.
- The bound is in entryMax (Σ₁ − Σ₂) with constant gaussCmpConst ι / v = O(n⁴)/v, dimension-dependent. Check that
  the printed Theorem 7.11 (chapters/inference.tex:132–141) tolerates dimension-dependent constants of this form;
  if the printed statement fixes a specific dimension dependence, a constant mismatch is a SOURCE-ISSUES item,
  not something to absorb silently.
- The left side uses `.real` (outer measure) on arbitrary convex K; downstream sup-over-convex-sets statements can
  use it directly without measurability side conditions.
- Corollary abs_real_convex_gaussCov_sub_le takes Γ ≥ 0 and the hypotheses on A⁻¹ diag(Γ) A⁻ᵀ; it relies on
  gaussCov_eq_map_mulVec / gaussCovFactor_mul_transpose from M4.1.
