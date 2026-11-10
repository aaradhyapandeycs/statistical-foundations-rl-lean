# CRITIC: all-convex Thm 7.11 route, milestone M4.1 (Gaussian law identity)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Infrastructure review for the all-convex Theorem 7.11 route, not a source result: no COVERAGE row, statement-index entry or named-result change follows from it. Reviewed: M4.1 (Gaussian law identity), `Formalization/Probability/GaussianCovCompare.lean`. Planning notes cited below (route plan, M5a design and design check, M6a interface note) are local and not published; the route plan check is public as [critic-allconvex-p0.md](critic-allconvex-p0.md). Probes are local scratch files (`<local probe>`).

Reviewed: Formalization/Probability/GaussianCovCompare.lean (219 lines,
sha256 52befd102b3e90473b65039a51e3540c81ef19b39948cc02948a5ad5c793067d, matches builder STATUS).
Critic probe: <local probe> (imports Formalization + the module).

## Verdict: ACCEPT WITH FIXES (one naming fix F1 before integration; F2 integration step)

The mathematics is sound and the exports are exactly what the M5a design (not published) L33 / M6 need.

## Evidence (commands actually run)
- `bash scripts/lean-local.sh Formalization/Probability/GaussianCovCompare.lean` (no -o, no artifact
  writes; pgrep showed 0 lean processes): exit 0, no errors, no warnings, ~3 s.
- `bash scripts/lean-local.sh <local probe>`: `#print axioms` on all 15
  module declarations (map_mulVec_stdGaussianPi_eq, charFunDual_gaussianReal_zero_one,
  charFunDual_stdGaussianPi, charFunDual_map_mulVec_stdGaussianPi, dual_apply_eq_dotProduct,
  dualVec_comp_mulVecCLM, coe_mulVecCLM, measurable_mulVec, exists_mul_transpose_eq_of_posSemidef,
  exists_square_factor_map_eq, gaussMap_eq_mulVec, gaussCov_eq_map_mulVec, gaussCovFactor_mul_transpose,
  gaussCov_eq_map_mulVec_of_mul_transpose, isProbabilityMeasure_map_mulVec_stdGaussianPi):
  all [propext, Classical.choice, Quot.sound].
- grep sorry/admit/axiom/set_option in the module: none.
- Probe errors are only the deliberate collision tests (below).

## Review points
R1 (char.-function route) SOUND. Uses Mathlib `charFunDual` on `ι → ℝ` (sup norm; not inner
product, so charFun would not apply). `Measure.ext_of_charFunDual` needs NormedSpace ℝ, BorelSpace,
SecondCountableTopology, CompleteSpace and two finite measures: all hold for finite `ι → ℝ` with the pi
sigma-algebra (instances found by elaboration; IsFiniteMeasure from the local IsProbabilityMeasure
instance on the map). `charFunDual_pi` (SigmaFinite gaussianReal) and `charFunDual_map` (CLM `mulVecCLM`,
coe lemma proved) are used with their real hypotheses. 1-D step reduces to Mathlib `charFun_gaussianReal`
via linearity `L x = L 1 * x`. Formula exp(-aᵀRRᵀa/2), a = dualVec L, checked: dualVec(L∘R) = Rᵀa.

R2 (gaussCov identification) CORRECT. `gaussCov A Γ` (TDInference711Defs.lean:143) is literally
`(Measure.pi fun _ ↦ gaussianReal 0 1).map (gaussMap A Γ)` with `gaussMap A Γ z = A⁻¹ *ᵥ (√Γ ⊙ z)`;
`stdGaussianPi` is the same pi measure (defeq, rw closes). `gaussCov_eq_map_mulVec` needs no hypotheses.
Γ ≥ 0 is used only in `gaussCovFactor_mul_transpose` (√Γ·√Γ = Γ) and is necessary there: probe confirms
`gaussCovFactor 1 (fun _ ↦ -1) = 0`, whose Gram is 0 ≠ diag(-1). Sufficient: yes. No invertibility of A
is assumed anywhere; statements are about Lean's `A⁻¹` (junk 0 if singular) and remain true then
(probe: A = 0 instance typechecks). Consumers needing a true inverse must supply IsUnit themselves (L33
does, via L32), nothing hidden here.

R3 (square factor) CORRECT. `S.PosSemidef → ∃ Q, Q * Qᵀ = S` via
`CStarAlgebra.nonneg_iff_eq_star_mul_self` under scoped MatrixOrder and `nonneg_iff_posSemidef`; Q = Bᵀ,
star = transpose over ℝ. Hypothesis is the standard real PSD predicate (symmetric + nonneg quadratic
form), the right one.

R4 (fit to the M5a design (not published)) MATCHES. L33 needs `twinLaw L = ν.map (Q *ᵥ ·)` with
`twinMat L univ : Matrix ι (κ × ι) ℝ` (rectangular) and square `Q : Matrix ι ι ℝ`:
`map_mulVec_stdGaussianPi_eq (twinMat L univ) Q hL30.symm` has exactly this shape (independent column
types κ, κ', arbitrary universes). §7.4 "γ_Σ = ν.map(Q·) with QQᵀ = Σ" is
`exists_mul_transpose_eq_of_posSemidef` + `map_mulVec_stdGaussianPi_eq`; M6 link to the TD limit law is
`gaussCov_eq_map_mulVec_of_mul_transpose`. (DESIGN §5 text says "charFun/ext_of_charFun"; the build uses
charFunDual instead, which is the correct choice for the sup-norm carrier. Doc-only drift.)

R5 (hidden hypotheses / non-vacuity) NONE HIDDEN. Only hypotheses: Fintype, the Gram equality, Γ ≥ 0,
PSD. Builder non-vacuity (Z₁+Z₂ ~ √2·Z, mass 1) compiles; critic added an independent one through the
gaussCov route: `gaussCov 1 (fun _ ↦ 2) = (stdGaussianPi (Fin 2)).map (!![1,1] *ᵥ ·)` — compiles.

## Fixes
F1 (required before any consumer imports both modules) NAME COLLISION.
`StatisticalRL.Probability.gaussMap_eq_mulVec` collides with existing
`StatisticalRL.Ch7Rest.TDInference.gaussMap_eq_mulVec` (TDInferenceSmooth711.lean:60). That file opens
`StatisticalRL.Probability` inside namespace `...TDInference`; with both opened the probe gives
"Ambiguous term @gaussMap_eq_mulVec". TDInferenceSmooth711 uses it in `simp_rw`/`rw` (lines 76, 151), so
any M6 module importing both would break or behave unpredictably. Rename, e.g. to
`gaussMap_eq_gaussCovFactor_mulVec` (one use site in this file). Other short names (measurable_mulVec,
mulVecCLM, dualVec, exists_mul_transpose_eq_of_posSemidef) have no root/Mathlib clash.
F2 (integration) The module is not imported by Formalization.lean, so the repo axiom audit does not
cover it yet; add the import when landing (critic audit above covers it now).
F3 (optional) `tdGaussFactor M π μ` (TDInferenceSmooth711.lean:45) is definitionally
`gaussCovFactor (tdA M π μ) (trueGamma M π μ)`; a one-line bridge lemma would let M6 reuse
`gaussCov_eq_map_mulVec_of_mul_transpose` directly. Not blocking.

Infrastructure only; no source result is claimed proved by this module, consistent with its docstring.
