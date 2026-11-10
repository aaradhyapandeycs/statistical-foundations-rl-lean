# CRITIC M6a: TD reservoir condition and gaussCov prerequisites (all-convex Thm 7.11 route)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Infrastructure review for the all-convex Theorem 7.11 route, not a source result: no COVERAGE row, statement-index entry or named-result change follows from it. Reviewed: M6a (TD reservoir condition and Gaussian target), `Formalization/Ch7Rest/TDInferenceConvexReservoir711.lean`. Planning notes cited below (route plan, M5a design and design check, M6a interface note) are local and not published; the route plan check is public as [critic-allconvex-p0.md](critic-allconvex-p0.md). Probes are local scratch files (`<local probe>`).

Integration (2026-11-09): F2 applied (`gaussCov_eq_map_inv_mul_diagonal_sqrt` is now a documented alias proved by M4.1's `gaussCov_eq_map_mulVec`, signature unchanged); F3 applied (the module docstrings of this module and of `GaussianIBP.lean` no longer reference local planning files); F4 applied as I1 of the M5a-2 review (the duplicate `ReservoirCond` and `matrixMaxRowAbsSum_le_of_forall` were deleted here, `ConvexLindebergReservoirBase.lean` is imported, and the module is imported from `Formalization.lean`); F5 applied (`dotProduct_self_nonneg'` is `private`). F1 concerns local planning notes only. Line numbers below refer to the reviewed version.

Critic: independent (not the builder). Date: 2026-11-09.
Under review: `Formalization/Ch7Rest/TDInferenceConvexReservoir711.lean` (685 lines, mtime 19:31).
Briefs: the route plan (not published) §4 M6, [critic-allconvex-p0.md](critic-allconvex-p0.md) §3/F7, the M5a design check (not published) R8/R11,
the M5a design (not published) §3 (contract) and L31/L32/L33.

## Verdict: **ACCEPT WITH FIXES** (all fixes are minor and non-mathematical; no fix changes a signature)

The mathematics is correct. The statements match the brief. Nothing is hidden. Everything is axiom-clean. The
fixes are naming, documentation and library hygiene.

## Evidence (my own compile)

- Probe: `<local probe>`, output in `<local log>`. It imports
  `Formalization`, `Probability.GaussianConvexShell` (M1), `Probability.GaussianCovCompare` (M4.1) and the module.
  It opens both `StatisticalRL.Probability` and `StatisticalRL.Ch7Rest.TDInference`.
- Command: `bash scripts/lean-local.sh <local probe>`, run only after
  `pgrep -x lean | wc -l` was below 2. Result: EXIT 0, no errors, no warnings.
- Axioms: all 16 key exports report exactly `[propext, Classical.choice, Quot.sound]`.
- Source scan: grep finds no `sorry`, `admit` or `axiom` in the module.
- Name collisions:
  - Every module declaration name was grepped across `Formalization/` and the M5a/M4.2 WIP folders. There are
    no duplicates.
  - With M4.1 imported and both namespaces open, `#check` resolves every short name with no ambiguity. That
    includes `gaussCov_eq_map_inv_mul_diagonal_sqrt` next to M4.1's `gaussCov_eq_map_mulVec`.
- Checked in the probe:
  - (3) the M5a `hcov` shape on `κ = Fin T`;
  - (4) `linPart = ∑_{k:Fin T} linSummand T k (ω k)`, so these are the actual summands;
  - (5) the Fin-indexed `∑ L_k L_kᵀ = linCov T`;
  - (6) `ReservoirCond … 1` ⇒ M5a L32 (`c·I ≤ Σ`);
  - (7) the L31 filter identity `n − (n−1−k) ≤ m ↔ k < m`;
  - (8) non-triviality: `¬ ReservoirCond refl 0 1 1`, so the predicate is not vacuous for `c > 0`;
  - (9) constant bookkeeping `2c = λT`;
  - M6a's factor `tdGaussFactor` is `rfl`-equal to M4.1's `gaussCovFactor (tdA) (trueGamma)`.

## Item-by-item reconstruction

**(1) ReservoirCond is the right object, byte-identical (R8).**
- A Python comparison of the def block in the M6a interface note (not published), the M5a design (not published) §3 and module :65–70 gives three equal
  strings.
- Semantics: "last r swapped" = `{e m | m ≥ n − r}`. At M5a step k the reservoir is `{e m | k < m}`, with
  r = n−1−k (L31). r = n gives L32. The quadratic forms are Euclidean, and the scaling is `c·r/n` (ℕ casts,
  real division).
- This matches DESIGN L20's `hv` shape after L31.

**(2) linFactor is the covariance factor.**
- `linSummand T k x = −T^{-1/2} W_k ξ_x`, and `E[ξ_u ξ_v] = δ_uv Γ_true(u)` (`sum_tupleProb_mul_sum_noiseVec_mul`).
  So `Cov(Y_k) = T⁻¹ W_k diag(Γ) W_kᵀ`.
- `L_k = T^{-1/2} W_k diag(√Γ)` gives `L_k L_kᵀ = T⁻¹ W_k diag(Γ) W_kᵀ` (√ is valid because `Γ_true ≥ 0`).
- The sign and the `1/√T` scaling are consistent: `(√T)⁻¹² = T⁻¹`.
- The summed identity equals `linCov` exactly (`linCov` is `T⁻¹ • Σ_{range T}`). The `hcov` lemma is entrywise
  and exact, not an inequality.

**(3) Duality, threshold, constants, counting.**
- `‖xM‖₁ ≤ (max row sum M)·‖x‖₁` is correct: it is the ℓ¹→ℓ¹ norm of Mᵀ, which is the ∞→∞ norm of M.
- `‖u‖₁ = ‖(uA⁻¹)A‖₁ ≤ α‖uA⁻¹‖₁ ≤ α(‖uW‖₁ + θ‖u‖₁)`, and with `θ ≤ 1/(2α)` this gives `‖uW‖₁ ≥ ‖u‖₁/(2α)`. ✓
- `tdA = diag(μ)(I − γP_π)`: row abs sum `≤ μ(s)(1+γ) ≤ 2`, so α = 2 and θ = 1/4. ✓
- F7 is honoured: the ∞→∞ norm comes from `norm_linWeight_sub_inv_mulVec_le` (sup norm on `State → ℝ`), via
  `sum_abs_le_of_norm_mulVec_le` (sign vector, correct). There is no √S in θ. The S factor enters once, through
  ℓ¹→ℓ² Cauchy–Schwarz (`‖uW‖₁² ≤ S‖uW‖₂²`), together with `‖u‖₂² ≤ ‖u‖₁²`.
- `uᵀLLᵀu = c²Σ_j (uW)_j² Γ_j ≥ c²γ‖uW‖₂² ≥ c²γ‖u‖₁²/(4α²S) ≥ c²γ‖u‖₂²/(4α²S)`. With c² = 1/T and α = 2 this is
  `γmin/(16ST)`. ✓
- Markov: `#bad/4 ≤ Σ_{k<T} e_k ≤ G T^{2/3}/η₀` (`sum_linWeightGap_le`, the same coefficient by definition). So
  `#bad ≤ 4G T^{2/3}/η₀`.
- `2#bad ≤ T` ⇔ `T^{1/3} ≥ 8G/η₀` ⇐ `T ≥ ⌈(8G/η₀)³⌉₊`. ✓ The condition k ≤ T is satisfied because k < T.
- Bad-first ordering:
  - for `r ≤ n − |B|`, all of the last r indices are good, giving `λr ≥ cr/n`;
  - otherwise the last r indices contain all `n − |B| ≥ max(n/2, r/2)` good indices, giving `λ(n−|B|) ≥ λr/2`.
  - Both cases need only `2c ≤ λn`. With `λ = γ/(16ST)` and `n = T`, `c = γ/(32S)` and r₀ = 1. ✓ This matches
    the P0 CHECK §3 ("r₀ = 1 and constant c/2").

**(4) gaussCov.**
- `gaussMap A Γ z = A⁻¹(√Γ ⊙ z) = (A⁻¹ diag √Γ) z`, a linear map with no shift, which is correct for a centred
  target.
- The inverse is `diag(1/√Γ)A`. Its row sums are `≤ 2/√γmin`. The shell constant `4S²(2/√γmin) r/√(2π)` follows
  from M1. ✓

**(5) Hidden hypotheses and non-vacuity.**
- `T ≥ linReservoirBurnIn` is explicit and disclosed. `0 < η₀ ≤ 1` and `0 < μmin ≤ μ` match the existing
  kernel exports.
- `exists_linFactor_reservoirCond` assumes only `0 ≤ γmin`, and at γmin = 0 it is trivially true (c = 0). R11 is
  addressed by `exists_linFactor_reservoirCond_of_pos`, which needs `Γ_true ≻ 0` and `[Nonempty State]` and
  returns `0 < c` together with the condition.
- The shell lemmas need `0 < γmin`, as they must.
- The builder's probe instantiates instance G (`Γ_true = (25/128, 1/128)`), for both the reservoir (also at
  T = burn-in) and the shell. I re-read it: the hypotheses are discharged honestly. My item (8) confirms that the
  predicate has content.

## Fixes

- **F1 (name mismatch, docs).** the M6a interface note (not published) (§"What M6a provides") and the M5a design (not published) §3(iii) cite
  `sum_tupleProb_mul_linSummand_mul_linSummand`. The actual export is `sum_tupleProb_mul_linSummand_mul`. Correct
  the two docs, or add the long name as an alias. Do not change the signature.
- **F2 (duplication with M4.1).** `gaussCov_eq_map_inv_mul_diagonal_sqrt` is the same statement as M4.1's
  `gaussCov_eq_map_mulVec` (`gaussCovFactor` unfolds to the same matrix; `tdGaussFactor = gaussCovFactor … := rfl`).
  - At integration, either import `GaussianCovCompare` and prove it by `gaussCov_eq_map_mulVec A Γ` (or drop it in
    favour of M4.1), or document it as a deliberate alias. That keeps the library free of parallel APIs.
  - Optional: state `inv_mul_diagonal_sqrt_eq` and the related lemmas in terms of `gaussCovFactor`.
- **F3 (public-release hygiene).** The module docstring references ignored private planning files
  (the M6a interface note, the route plan, the design check; none published). These are dead links
  in the public repo. Replace them with self-contained descriptions, or point to a `docs/` file. `GaussianIBP.lean`
  has the same pattern, so the lead may sweep both.
- **F4 (integration, R8; lead).** In one commit:
  - move `ReservoirCond` verbatim to `ConvexLindebergReservoir.lean`;
  - delete the copy at :60–70;
  - add the import to this module;
  - add the module to `Formalization.lean`. It is not imported there yet, so the repo-wide axiom audit does not
    cover it until this is done.
- **F5 (cosmetic, optional).** The name `dotProduct_self_nonneg'` in `StatisticalRL.Probability` is generic.
  Mathlib has `dotProduct_self_star_nonneg` and related lemmas. Consider using Mathlib's lemma, or making this one
  private.

## Notes for consumers

- **M5a:**
  - Take `κ = Fin T`, `n = T`, `L = fun k : Fin T ↦ linFactor … T k`, `p i = tupleProb` and
    `Y i = linSummand … T i`.
  - Inputs: `hmean` = `sum_tupleProb_mul_linSummand`; `hcov` = `sum_tupleProb_mul_linSummand_mul`; `hr₀ : 1 ≤ T`
    from `one_le_linReservoirBurnIn`; `hc` from `_of_pos`.
  - The predicate is fixed. Do not alter binders or casts.
- **M6.3:**
  - `twinLaw L` has covariance `Σ_{k:Fin T} L_kL_kᵀ = linCov T`. Use the Fin form (probe item 5:
    `Fin.sum_univ_eq_sum_range` + `sum_linFactor_mul_transpose`).
  - Compare with `gaussCov tdA Γ_true` through M4.1 `gaussCov_eq_map_mulVec_of_mul_transpose`.
  - The target's shell constant is `tdGaussCov_convexShell_le(_diagMin)`, i.e. `8S²/√(2π γmin)`. Separately,
    M5a L33 has `√(S/c)` with `c = γmin/(32S)`, i.e. `S·√(32/γmin)`.
- **M7:**
  - Every TD-side constant depends on `γmin = diagMin Γ_true > 0`, `μmin` and `η₀`.
  - Small T (`T < linReservoirBurnIn`) must be absorbed into K (`β ≤ 1 ≤ K T^{-1/3}` when
    `K ≥ burnIn^{1/3}`), as F4 of the P0 CHECK says.
  - The burn-in is `⌈(8G/η₀)³⌉₊` with `G = 3K_β² + 1/a²`. It is large but finite and explicit.
