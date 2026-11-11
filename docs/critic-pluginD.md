# Critic review: item D, plug-in-covariance coverage (C47 correction)

Public copy of the independent critic report; local paths removed. Probe and draft files named below (`reviewer-probes/`, `DRAFT-STATEMENT.lean`) were kept in private folders and are not published.

Post-review note (added to this public copy, 2026-11-09): F1, F2 and R1 were applied to the module docstring of `TDInferencePluginCoverage711.lean` and to the entry docstring. F3 was applied: the module is imported by `Formalization.lean` and `Formalization/Statements/Ch7Proofs.lean`, the entry `Eq_convex_Cdelta_corrected_plugin` follows `Eq_convex_Cdelta_corrected_oracle` in `Formalization/Statements/Ch7.lean`, and the full `Audit.lean` axiom audit passes. The COVERAGE, C47 and ERRATA texts below were adopted. R2 and R3 remain open. The review text below is otherwise unchanged.

Reviewer: independent critic (not the builder). Date 2026-11-09.

## Verdict: ACCEPT WITH FIXES

The fixes are documentation and integration only. The mathematics and the Lean proofs are correct, and the
draft entry states what is proved.

## Under review (hashes)

- `Formalization/TDInference/PluginCovariance/Coverage.lean`, sha256 `19dd28f2…8d06`, 449 lines.
- the builder's draft statement file `DRAFT-STATEMENT.lean`, sha256 `d13b988c…b32f`.
- Source `source/upstream/tex/chapters/inference.tex`, sha256 `82707713…648f2`, which matches the C47 pin.
  Rule :187–196 (display :191–193, claim :196), rectangles :198–205, ellipsoids :207–213, plug-in :156–185
  (`eq:defn-hat-Lambda` :180–182), step-size range `0<η₀<1/4` :133.

## Commands and evidence (one Lean process at a time; `pgrep -x lean` was 0 before each run)

- `bash scripts/lean-local.sh Formalization/TDInference/PluginCovariance/Coverage.lean`: clean, no output.
- `reviewer-probes/CriticEntry.lean`: the draft entry, importing only `Formalization.TDInference.Definitions`.
  Clean, so G2 is satisfied, and `Statements/Ch7.lean` already imports that module.
- `reviewer-probes/CriticProbe.lean`: imports `Formalization` and the new module, then the entry and the wrapper.
  Clean, with no name collisions. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for
  `Eq_convex_Cdelta_corrected_plugin_holds`, `tendsto_pathProb_le_mul_sqrt_quadForm_lambdaHat`,
  `plugin_coverage_tendsto`, `eventually_coverage_rect_plugin_ge` and `oneState_tendsto_coverage_oneSided_plugin`.
- `reviewer-probes/CriticJunk.lean`: independently proves `(aBar M ω).det = 0 → lambdaHat M η₀ V₀ ω = 0`, which
  confirms the junk value. Clean.
- A grep for `sorry`, `admit` and `axiom` in the module and the draft found nothing.
- Not run: `lake build`, `scripts/check.py`, and the full `Audit.lean`. The module is not yet imported by
  `Formalization.lean`.

## Independent reconstruction and attacks

**(1) Sandwich, D1 core.** Let q = uᵀΛu with Λ = trueLambda = A⁻¹diag(Γ_true)A⁻ᵀ, so q > 0 by
`quadForm_oracle_pos`. Let q̂ = uᵀΛ̂u and B = {∃ s,s', |Λ̂_ss' − Λ_ss'| > ε₁}.

- Off B: |q̂ − q| ≤ (∑|u_s|)²ε₁ (`abs_quadForm_sub_le`), and |√q̂ − √q| ≤ |q̂ − q|/√q. The second bound holds for
  every real q̂ because √ of a negative number is 0 (`abs_sqrt_sub_sqrt_le_div`, checked for both cases). Hence
  |z√q̂ − z√q| ≤ ε.
- The proof works with |z| and needs no sign case on z, so D1 holds for every z ∈ ℝ. That is correct.
- E ⊆ H(z√q+ε) ∪ B and H(z√q−ε) ⊆ E ∪ B. The half-space probabilities at c = z√q ± ε, rescaled by √q, are within
  K·T^(-1/3) of Φ(z ± δ/2). The pivot export is uniform in the threshold, so evaluating it at a z-dependent
  threshold is legitimate.
- Φ is continuous at z, P(B) → 0 by `eq_defn_hat_Lambda_corrected`, and K·T^(-1/3) → 0. Each error term is at
  most η/3, so the total is below η. The arithmetic is correct.

**D2 (two-sided, z ≥ 0).** 1{|w| ≤ c} = 1{w ≤ c} + 1{−w ≤ c} − 1 requires c ≥ 0. Here c = z√q̂ ≥ 0 needs z ≥ 0,
and for z < 0 the target 2Φ(z) − 1 would be negative, so the restriction is necessary and correct. Flipping u to −u
leaves q̂ unchanged.

**D3 (Bonferroni box).** The box applies D2 with u = e_s, where e_sᵀΛ̂e_s = Λ̂_ss (`quadForm_single`). The union
bound is P(∩E_s) ≥ 1 − ∑(1 − P(E_s)), and its limit is 1 − 2S(1 − Φ(z)). The "eventually ≥ limit − η" form is
correct. The statement is vacuous for small z, where 1 − S − η ≤ 0, as Bonferroni boxes are. That is not a defect.

**Path-event bridges.** `sub_mul_sqrt_div_le_iff`, `abs_le_mul_sqrt_div_iff` and `sum_mul_scaledError` give
uᵀV̄ − z√(q̂/T) ≤ uᵀV^π ⇔ uᵀ√TΔ̄ ≤ z√q̂ for T > 0, with scaledError = √T(V̄ − V^π). The orientation is correct: the
lower one-sided interval for uᵀV^π has coverage Φ(z).

**(2) Junk inverse.** If Ā_T is singular, Lean's `Matrix.inv` returns 0, so lambdaHat = 0 (re-proved in
`CriticJunk.lean`). The proof does not need the singular event to lie inside B. B is defined from `lambdaHat`
itself, so on every ω either Λ̂ (junk or not) is entrywise within ε₁ of Λ and the threshold bound applies, or
ω ∈ B and the probability is charged there. The junk value therefore cannot break the argument.

Under Γ_true ≻ 0, Λ_ss = ∑_k Γ_k((A⁻¹)_sk)² > 0, because row s of the invertible A⁻¹ is nonzero. So the singular
event (Λ̂ = 0) does lie inside B whenever ε₁ < min_s Λ_ss. The CHECK remark "inside Eᶜ when δ < 1" is the same
fact. However, the ε₁ in the proof is not chosen that small, so the module and entry phrase "that event lies in the
bad event and is charged there" is slightly imprecise (F1).

A consequence: any measurable definition of the procedure on the singular event gives the same limits, because
P(singular) ≤ ∑_s(1 − μ_s)^T → 0.

**(3) Hypotheses.**
- Γ_true ≻ 0 is used twice: in the half-space export and for q > 0.
- It is essentially necessary. If Γ_true(s) = 0 for some s, take u = Aᵀe_s; then q = 0 and the √q rescaling fails.
  In the fully zero-noise instance (`zMDP`), uᵀ√TΔ̄_T is deterministic, so coverage tends to 0 or 1, not Φ(z).
- The hypothesis is disclosed.
- No hidden hypotheses. `[Nonempty State]` and `[Nonempty Action]` are harmless. The export assumes `η₀ ≤ 1`,
  which is weaker than the printed `η₀ < 1/4`; the entry states the printed range and the wrapper weakens it with
  `linarith`. That is the allowed direction.

**(4) Entry honesty.**
- The name `Eq_convex_Cdelta_corrected_plugin` carries `_corrected` (CHECK fix) and is distinct from `_oracle`.
- The Prop is self-contained. It mentions only data-computable objects (`prAverage`, `lambdaHat`,
  `valueFixedPoint`, `pathWeight`), plus `trueGamma` in a hypothesis. `trueLambda` does not appear, which is right
  because the printed rule uses only Λ̂_T.
- It makes qualitative limit claims only, with no rate, and the docstring says so.
- It excludes data-selected convex sets, the ℓ∞-quantile rectangle and the ellipsoid, and the docstring says so.
- The Prop matches the export exactly, and the wrapper is a direct application with no reproof.

**(5) Non-vacuity.** `oneState_tendsto_coverage_oneSided_plugin` instantiates every hypothesis
(μ = 1, Γ_true = 1/4, η₀ = 1/8 ∈ (0, 1/4), u = 1). So the hypotheses are jointly satisfiable, and the conclusion
is a genuine limit statement about a probability. Ā_T = 1/2 surely there, so this instance does not exercise the
singular event. That is optional to add (an S = 2 instance) and is not required.

## Findings

- **F1 (required, wording).** The junk sentence in the module docstring and in entry item (4) should read
  something like: "On that event Lean's `lambdaHat` is 0 and the interval degenerates to the point estimate. No
  special handling is needed: the proof charges every outcome with Λ̂_T entrywise ε₁-far from Λ, and since
  diag Λ ≻ 0 under Γ_true ≻ 0 the singular event is contained in that bad event for small ε₁. Its probability is
  at most ∑_s(1−μ(s))^T → 0 (`pathProb_aBar_singular_le`), so the limits do not depend on how the procedure is
  defined there."
- **F2 (required, wording).** Entry item (3) attributes the Γ_true ≻ 0 assumption to C43. Split these: Γ_true ≻ 0
  is an added non-degeneracy hypothesis (needed for uᵀΛu > 0 and for the half-space result), and separately C43
  explains why the target covariance is A⁻¹diag(Γ_true)A⁻ᵀ rather than the printed Λ⋆.
- **F3 (required, integration).** Add `import Formalization.TDInference.PluginCovariance.Coverage` to
  `Formalization.lean` and to `Statements/Ch7Proofs.lean`. Place the entry after `Eq_convex_Cdelta_corrected_oracle`.
  Then run `python3 scripts/check.py`. This critic did not run the full audit.
- **R1 (recommended).** State in the docstring that the limits are pointwise in (u, z), not uniform.
- **R2 (recommended).** The plug-in version of the C47(1) refutation is now within reach. With sign-selected
  half-lines of radius z√(Λ̂_T/T), coverage equals P(|√TΔ̄_T| ≤ z√Λ̂_T), which tends to 2Φ(z) − 1 by D2. This
  holds as long as the "conditional mass exactly Φ(z)" part (Λ̂_T > 0) is handled. Optional follow-up.
- **R3 (optional).** Add an S = 2 non-vacuity instance in which the singular event has positive probability.

## Recommended entry docstring

```
/-- Corrected (fixed-shape) variant, with the printed plug-in covariance, of the confidence-set rule
`eq:convex.Cdelta` (`chapters/inference.tex:187–196`, display :191–193, claim :196); plug-in `Λ̂_T` from
`eq:defn-hat-Lambda` (:180–182); rectangle prose :198–205. See `docs/SOURCE-ISSUES.md#C47` and `#C43`.

Differs from the printed text: (1) the printed claim for arbitrary convex sets chosen from the data is false
(C47(1)); here the direction `u` and level `z` are fixed before the data (the C47 proposed correction): one-sided
half-lines, two-sided intervals for a linear functional `uᵀV^π`, and a Bonferroni box with the plug-in diagonal
`Λ̂_T(s,s)`. (2) Asymptotic coverage only, pointwise in `(u, z)`: the plug-in consistency
`Eq_defn_hat_Lambda_corrected` has no rate, so no finite-`T` bound is claimed. (3) Added non-degeneracy hypothesis
`Γ_true ≻ 0` (so `uᵀΛu > 0` for `u ≠ 0`, with `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`, the limit of `Λ̂_T`; by C43 this differs
from the printed `Λ⋆` unless rewards are state-only). (4) Junk value: when some state is unsampled `Ā_T` is singular
and the printed `Λ̂_T` is undefined (C47(4)); Lean's `Matrix.inv` returns 0, so the interval degenerates to the point
estimate there. That event has probability ≤ ∑_s(1−μ(s))^T → 0 and lies inside the consistency bad event, so the
limits do not depend on the convention. Not covered: data-selected convex sets (C47(1)), the printed `ℓ∞`-quantile
rectangle (C47(2)), the ellipsoid (C47(3)), any rate. Kept: i.i.d. sampling, full-support `μ`, `0 < η₀ < 1/4`
(:133), every `V₀`.

Statement, with `Φ(z) = N(0,1)(−∞, z]`, `S = |State|`, `Λ̂_T = lambdaHat`:
(1) all `u ≠ 0`, `z ∈ ℝ`: `P(uᵀV̄_T − z√(uᵀΛ̂_Tu/T) ≤ uᵀV^π) → Φ(z)`;
(2) `u ≠ 0`, `z ≥ 0`: `P(|uᵀ(V̄_T − V^π)| ≤ z√(uᵀΛ̂_Tu/T)) → 2Φ(z) − 1`;
(3) `z ≥ 0`, `η > 0`: eventually `P(∀ s, |V̄_T(s) − V^π(s)| ≤ z√(Λ̂_T(s,s)/T)) ≥ 1 − 2S(1 − Φ(z)) − η`. -/
```

## COVERAGE update for `eq:convex.Cdelta`

The row stays **Partial** and cannot drop it. The printed ℓ∞-quantile rectangle (C47(2)) and the ellipsoid
(C47(3)) are neither formalized nor machine-refuted, and the general data-selected rule is false (C47(1)).

Suggested edits:

- Add `TDInferencePluginCoverage711.lean` to the files column.
- In the status text, after the oracle sentence, add: "With the printed plug-in Λ̂_T (`Eq_convex_Cdelta_corrected_plugin`,
  export `plugin_coverage_tendsto`): for u and z fixed before the data, one-sided coverage → Φ(z), two-sided
  (z ≥ 0) → 2Φ(z) − 1, and the Bonferroni box with half-widths z√(Λ̂_T(s,s)/T) eventually ≥ 1 − 2S(1 − Φ(z)) − η.
  These are asymptotic only, with no rate (plug-in consistency has none), under the same hypotheses including
  Γ_true ≻ 0. Lean's junk Λ̂_T = 0 on the singular event does not affect the limits."
- Replace the "Open:" list with: "Open: a finite-T rate for the plug-in rule; the printed ℓ∞-quantile rectangle
  (C47(2)); the ellipsoid (C47(3)); the C47(1) refutation with Λ̂_T (still a paper argument, now a near-corollary of
  D2); a finite-T definition of the printed procedure on the singular event (C47(4))."
- Add "[review](critic-pluginD.md)" when this report is promoted to `docs/`.

## C47 addendum (proposed text)

**Fixed-shape correction, plug-in covariance (2026-11-09, `Formalization/TDInference/PluginCovariance/Coverage.lean`,
entry `Eq_convex_Cdelta_corrected_plugin`).** The proposed correction is machine-checked with the printed estimator
Λ̂_T = Ā_T⁻¹Γ̂_TĀ_T⁻ᵀ, asymptotically. For a direction u and level z fixed before the data, under full-support i.i.d.
sampling, 0 < η₀ < 1/4, every V₀ and Γ_true ≻ 0:

- the one-sided interval has coverage → Φ(z);
- the two-sided interval (z ≥ 0) has coverage → 2Φ(z) − 1;
- the Bonferroni box with half-widths z√(Λ̂_T(s,s)/T) has coverage eventually ≥ 1 − 2S(1 − Φ(z)) − η for every
  η > 0.

The proof sandwiches the random threshold between deterministic half-spaces off the event where Λ̂_T is entrywise
far from A⁻¹diag(Γ_true)A⁻ᵀ. It uses the half-space result of [C43](#C43) and the corrected consistency
`eq_defn_hat_Lambda_corrected`. No rate is given.

For (4): Lean's convention Λ̂_T = 0 on the singular event (a degenerate interval) does not affect the limits.
Because that event has vanishing probability, any definition there gives the same asymptotic coverage. The printed
procedure is still undefined there for finite T.

Still open: a rate, (2), (3), and the Λ̂_T version of the (1) refutation. Independently critic-reviewed
([review](critic-pluginD.md)). Not author-approved.

## ERRATA note (item 23)

In the "Effect" paragraph, replace "The plug-in coverage rule … remain open" with: "With the printed plug-in Λ̂_T,
fixed-shape intervals and the Bonferroni box are proved asymptotically valid (`Eq_convex_Cdelta_corrected_plugin`;
limits only, no rate; Γ_true ≻ 0 assumed; Lean's junk Λ̂_T = 0 on the singular event does not affect the limits).
The printed rectangle and ellipsoid, a finite-T rate for the plug-in rule, and a finite-T definition of the procedure
on the singular event remain open."
