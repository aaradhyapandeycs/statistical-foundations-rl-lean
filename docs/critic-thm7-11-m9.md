# Critic review: M9, Theorem 7.11 on closed half-spaces (corrected Γ)

Public copy of the independent critic report; local paths removed. Probe and scratch files named below (`reviewer-probes/`, `builder-probes/`) were kept in private folders and are not published.

Post-review note (added to this public copy, 2026-11-09): the entry was integrated under the recommended name `Thm7_11_corrected_halfspace` in `Formalization/Statements/Ch7.lean`, with the wrapper `Thm7_11_corrected_halfspace_holds` in `Formalization/Statements/Ch7Proofs.lean`, the corrected citations (F1) and the added docstring text (F2, F3), and the one G2 allowlist edge (R2). By the maintainer's decision the ledger record (§7) was added to `docs/named-result-status.json` as a `proved_variants` record, with the §7 wording conditions applied to README and PROGRESS. The review text below is otherwise unchanged.

Reviewer: independent source-fidelity critic (not the builder). Date 2026-11-09.

Under review:
- library export `StatisticalRL.Ch7Rest.TDInference.abs_lawProb_halfSpace_sub_gaussCov_le`
  (`Formalization/Ch7Rest/TDInferenceHalfSpace711.lean:396`), imported from `Formalization.lean:729`;
- draft entry and wrapper `Thm7_11_restricted_halfspace` (`builder-probes/DRAFT-STATEMENT.lean`).

Source: `source/upstream/tex/chapters/inference.tex` (pinned), theorem :132–141, setting :47–89, `Λ⋆`, `A`, `Γ`
:106–117, convex distance :124–129, confidence sets :150–213.

## Verdict: ACCEPT WITH FIXES

The mathematics is right and the export is genuine. The draft Prop states exactly what is proved. The fixes are:
- the name (R1);
- the docstring line citations and wording (F1–F3);
- one G2 allowlist edge (R2);
- the COVERAGE, C43, ledger and site text (R3–R5).

No library change is needed.

## 1. Reconstruction of the printed theorem

Printed (:132–141): consider the following setting.
- TD update (:72), only coordinate `s_t` changes, `r_t = r(s_t,a_t)`.
- i.i.d. tuples `s_t∼μ`, `a_t∼π(·|s_t)`, `s'_t∼P(·|s_t,a_t)` (:51–65), with `λ₀ = min μ > 0` (:67).
- Polyak–Ruppert average `V̄_T = T⁻¹∑_{t=1}^T V_t` (:82), `Δ̄_T = V̄_T − V^π` (:87).
- `η_t = η₀t^{-2/3}`, `0 < η₀ < 1/4` (:133).

Then
`d_cvx(√TΔ̄_T, N(0, A⁻¹ΓA⁻ᵀ)) ≲ (√(η₀/((1−γ)λ₀))Tr Γ‖Γ⁻¹‖ + √(Sκ(Γ))/((1−γ)λ₀η₀))T^{-1/3} + C̃T^{-1/2}`.
Here:
- `d_cvx` is a sup over all convex subsets of `ℝ^d`, with `d = S`;
- `A = diag(μ)(I−γP_π)` (:114);
- `Γ = diag(μ(s)E_{s'∼P_π}[(V^π(s) − r(s) − γV^π(s'))²])` (:115), where `r(s)` is undefined;
- `C̃` is "problem-related, polynomial".

The theorem does not quantify `V₀`. `‖Γ⁻¹‖` and `κ(Γ)` require `Γ ≻ 0`.

## 2. Binder and definition check (item 1)

I read every definition in `Formalization/Ch7Rest/TDInference711Defs.lean`.

| Printed item | Lean | Verdict |
| --- | --- | --- |
| sampling law (:51–67) | `tupleProb = μ(s)π(a|s)P(s'|s,a)`; `pathWeight` = product over `Fin T`; `lawProb … T C = ∑_ω pathWeight·1_C(scaledError ω)` (total mass 1, `lawProb_univ`) | exact; reward deterministic `M.reward s a` |
| μ full support | `∀ s, 0 < μ.prob s` | exact |
| TD update (:72) | `tdStep`: `Function.update V s ((1−η)V s + η(r(s,a) + γV s'))` | exact |
| `η_t = η₀t^{-2/3}` | `tdIter` builds `V_{t+1}` from `ω t` with `stepSize η₀ (t+1)`, so `V_1` uses `η_1 = η₀` | exact (no `0^{-2/3}` junk) |
| `0 < η₀ < 1/4` | entry `0 < η₀ → η₀ < 1/4`; the export needs only `η₀ ≤ 1` (wrapper `by linarith`) | exact (the export assumes less, which is allowed) |
| `V̄_T`, `√TΔ̄_T` | `prAverage = T⁻¹∑_{t<T} V_{t+1}`; `scaledError = √T(V̄_T − valueFixedPoint π)` | exact |
| `V₀` | `∀ V₀`, quantified before `∃ K` | stronger than or equal to printed; K depends on V₀ (disclosed) |
| `T` | `∀ T ≥ 1` | exact |
| `A` | `tdA = diagonal μ * (1 − γ•policyMatrix)`; invertible (`tdA_isUnit`, μ > 0, γ < 1), so `A⁻¹` is not junk | exact |
| `N(0, A⁻¹ΓA⁻ᵀ)` | `gaussCov A Γ` = pushforward of `∏N(0,1)` by `z ↦ A⁻¹(√Γ ⊙ z)`; covariance `A⁻¹diag(Γ)A⁻ᵀ`; a probability measure (instance) | exact |
| `Γ` | `trueGamma = μ(s)E_{a∼π}E_{s'∼P(s,a)}[(V^π(s) − r(s,a) − γV^π(s'))²]` | **changed object** (C43 correction) |
| `Γ ≻ 0` | `∀ s, 0 < trueGamma M π μ s` | definedness of the printed coefficient, transferred to the corrected Γ; disclosed, not hidden |
| set class | closed half-spaces `{x | ∑ u_s x_s ≤ b}`, uniformly in `u` (zero allowed) and `b` | **restriction** |
| constant | `∃ K > 0` before `∀ T u b`, depending on the instance, `η₀` and `V₀` | **restriction** (the coefficient is not the printed one; `C̃T^{-1/2}` is absorbed) |

The ambient conventions are inherited from `DiscountedMDP` and are standard across the project: rewards in [0,1],
`0 ≤ γ < 1`, and `Nonempty State`, `Nonempty Action`. With state-only rewards (`r(s,a) = r(s)`), `trueGamma` equals
`printedGamma` term by term, because the `s'` marginal under `a∼π`, `s'∼P(·|s,a)` is `P_π(·|s)`. This follows
immediately from the definitions but is not Lean-checked. Under that reading, the entry is a pure restriction of the
printed theorem.

## 3. Restriction and naming (item 2)

The entry differs from the printed theorem in three ways:
- (a) the covariance object changes (Γ → Γ_true), which repairs the printed theorem refuted in C43;
- (b) the set class shrinks to closed half-spaces;
- (c) the constant is instance-, η₀- and V₀-dependent.

**R1 (name).** Use **`Thm7_11_corrected_halfspace`**, not `Thm7_11_restricted_halfspace`.

1. AGENTS.md: an export that "concerns a different object" is a correction. The project's adopted reading (COVERAGE
   row, C43, `REFUTED_READING` in `site/reader/lean.py`) records the printed theorem as **refuted**. Calling the new
   entry `_restricted` reads as "a restricted case of a printed theorem". That is false under the adopted reading,
   because no restriction of a refuted statement with the printed Γ is proved.
2. Project precedent for corrected plus scope qualifiers: `Thm7_3_corrected_knownReward`,
   `Thm7_8_corrected_constSum`, `Thm7_12_corrected_local`.
3. The tooling classifies by name. `scripts/gen_nodes.py` `classify` (also used by the site) lets the substring
   `corrected` win, so either name shows only one of the two disclosures. "Proved in corrected form" is the less
   misleading one here. The half-space and constant restrictions must then be carried by the docstring, COVERAGE,
   ledger `statement_scope` and a site chip (R5).

A double suffix such as `_corrected_restricted_halfspace` adds nothing: the classifier ignores the second marker.
`_corrected_halfspace` already names the restriction.

## 4. Meaningfulness and overclaiming (item 3)

- **Not vacuous.** `M9Probe.instanceG` (`builder-probes/Probe.lean`) discharges every hypothesis on a 2-state instance with
  action-dependent rewards, which is exactly the reading in which the printed theorem is refuted. In that instance
  `Γ_true = (25/128, 1/128) ≻ 0`.
- **Gaussian side genuine.** `gaussCov_real_halfSpace` identifies the mass as `N(0, uᵀΛu)(−∞,b]`.
  `instanceG_gauss_pos_var` shows the variance is positive, so the mass is not a degenerate 0 or 1.
- **K finite and uniform.** `K` is chosen before `T`, `u` and `b`. I proved in my scratch file
  (`critic_rate_tendsto`, below) that the entry implies
  `sup_{u,b} |P(uᵀ√TΔ̄_T ≤ b) − N(…){uᵀx ≤ b}| → 0`. So the statement is a genuine T^{-1/3} rate, not just the
  trivial bound by 1.
- **Closed vs open half-spaces.** The same `K` holds for open half-spaces by monotone limits, because both laws are
  countably additive. Not stated in Lean; optional COVERAGE remark.
- **Overclaim check of the draft docstring.**
  - It does not claim convex sets, a universal constant, or confidence regions. Good.
  - It should also say explicitly:
    - (i) there is no confidence statement with the estimated covariance `Λ̂_T`: C47(1),(2),(4) are untouched,
      not only C47(3);
    - (ii) the all-convex corrected statement and the printed coefficient remain open.

## 5. Wrapper and compilation (item 4)

- The wrapper only `intro`s and applies `abs_lawProb_halfSpace_sub_gaussCov_le` with `by linarith` for
  `η₀ ≤ 1`. It is not a re-proof. G3's `HOLDS_HEADER_RE` (`: X` exactly) is satisfied.
- `Thm7_11_*` entries need `Formalization.Ch7Rest.TDInference711Defs`.
  - `Statements/Ch7.lean` does not import it, and `scripts/gates/g2_statement_imports.txt` (frozen, shrink-only)
    has no such edge.
  - **R2:** add the edge `Formalization/Statements/Ch7.lean -> Formalization.Ch7Rest.TDInference711Defs` with
    `python3 scripts/static_gates.py --write-allowlists --allow-grow`, and give the justification in the PR or
    commit message.
  - The justification: a definitions module (objects of :47–129 plus totality and measurability facts); no
    `*Proofs` module; no transitive import of the half-space proof module.
- `TDInference711Defs` imports `ModelFree.TDIterateBounds` (proof-bearing). Existing allowlisted edges
  (`Ch7Rest.FedGeneric710`) set the precedent. Acceptable.
- `Ch7Proofs.lean` must add `import Formalization.Ch7Rest.TDInferenceHalfSpace711` (proof file, not under G2's
  statement allowlist).
- G3 docstring rules are satisfied: the `.tex:a–b` range is present, and C43 and C47 are anchors (`C47(3)` matches
  `CID_RE`).

**Compile evidence (one Lean process at a time, `bash scripts/lean-local.sh`; oleans current: `Formalization.olean`
05:51 > `Formalization.lean` 05:50; `TDInferenceHalfSpace711.olean` 05:48 > source 05:47):**

- `reviewer-probes/StmtOnly.lean` imports **only** `Formalization.Ch7Rest.TDInference711Defs` and
  elaborates the renamed entry. rc=0, no output (`stmt.out`). This confirms the entry is G2-compatible with the one
  new edge.
- `reviewer-probes/Full.lean` imports `Formalization` and contains the entry, the wrapper and
  `critic_rate_tendsto`. rc=0 (`full.out`):
  - `Thm7_11_corrected_halfspace_holds` depends on axioms `[propext, Classical.choice, Quot.sound]`;
  - `critic_rate_tendsto` depends on axioms `[propext, Classical.choice, Quot.sound]`.
- Builder probe output (`builder-probes/probe.out`): all 13 exports of `TDInferenceHalfSpace711` use only those three axioms.
- Not run by me: `lake build`, `Audit.lean`, `scripts/check.py` (per brief). The lead reports the full audit passes.

## 6. Findings

- **R1** Rename to `Thm7_11_corrected_halfspace` (§3).
- **R2** Add the G2 edge with `--allow-grow` and a justification (§5).
- **R3** Update the COVERAGE row and add a C43 addendum (text below). Without the addendum, C43 still says "the
  corrected statement … including its convex-set bound, remains open", which stays true for all convex sets but
  must now mention the half-space result.
- **R4** Ledger: count it as a `proved_variants` record (§7).
- **R5** Site: add `CHIP_OVERRIDES["Thm7_11_corrected_halfspace"]` and a `CARD_NOTES` entry so the chip does not
  read as the full corrected theorem. `REFUTED_READING` stays, because the printed statement is still refuted under
  that reading.
- **F1** Docstring line citations are off:
  - sampling is `inference.tex:51–67` (full support at :67), not ":52–64";
  - `Λ⋆`, `A` and `Γ` are `:106–117` (A :114, Γ :115), not ":104–112";
  - the step-size hypothesis is at :133.
  - Minor, outside this change: `TDInference711Defs.lean` docstrings cite `tdA` at :110 (should be :114),
    `printedGamma` at :111 (:115) and `stepSize` at :134 (:133); C43 cites full support at `inference.tex:64`
    (should be :67).
- **F2** The docstring must say what the printed Γ omits (action-reward variance *and* the cross term
  `2γCov(r(s,a), V^π(s'))`, C43) and that Γ_true = Γ_printed under state-only rewards.
- **F3** The docstring must disclaim confidence statements with the estimated covariance (C47(1),(2),(4)) and say
  that the all-convex corrected statement and the printed coefficient remain open.

## 7. Ledger recommendation (item 5)

**Count it, as a `proved_variants` record, which moves 89/90 to 90/90.** Check against the private M4 plan check §2
item 3:

| Threshold condition | Result |
| --- | --- |
| Convex-set statement, all convex sets or a disclosed convex subclass "such as half-spaces" | met, closed half-spaces uniformly in `(u, b)` |
| True Γ (C43) | met |
| Printed rate T^{-1/3} | met |
| Constants disclosed: instance/V₀ `C̃` is a reading of "problem-related"; a changed coefficient must be stated | met in the docstring |

The result is also at least as strong as the counted precedent `Thm7_12_corrected`, whose printed rate is "neither
proved nor refuted". Here the printed rate is proved.

Conditions on counting:
- PROGRESS and README must say that 90/90 means every named result has *a proved form, possibly corrected or
  restricted*.
- They must say that Theorem 7.11's counted form is a half-space-only, instance-constant, corrected-Γ variant, and
  that the all-convex corrected bound is open.
- The complete monograph stays **INCOMPLETE**.

If the lead or user prefers not to reach 90/90 on a variant this far from the printed set class, that is a policy
choice. The threshold does not require it.

## 8. Recommended texts

### Entry (`Formalization/Statements/Ch7.lean`; import `Formalization.Ch7Rest.TDInference711Defs`)

```lean
open StatisticalRL StatisticalRL.Ch7Rest.TDInference in
/-- Theorem 7.11 (`thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`), corrected covariance, closed
half-spaces only, instance constant. Differs from the printed result in three ways.
(1) `Γ` is the true per-sample TD-noise covariance `trueGamma`,
`Γ_ss = μ(s) E_{a∼π(·|s), s'∼P(·|s,a)}[(V^π(s) − r(s,a) − γV^π(s'))²]`. The printed `Γ` (:115) averages only over
`s' ∼ P_π` with an undefined `r(s)`; read as `r_π(s)`, it omits the action-reward variance and a cross term, and the
printed theorem is then false (SOURCE-ISSUES C43). With state-only rewards the two coincide.
(2) The sets are closed half-spaces `{x | ∑ s, u s * x s ≤ b}` (uniformly in `u`, `b`), not all convex sets in
`ℝ^S`.
(3) The `T^{-1/3}` constant `K` depends on the instance, `η₀` and `V₀`. It is not shown to be a universal multiple of
the printed `√(η₀/((1−γ)λ₀))Tr Γ‖Γ⁻¹‖ + √(Sκ(Γ))/((1−γ)λ₀η₀)`, and `C̃T^{-1/2}` is absorbed into `K`, so it is not
shown polynomial.
Kept: the printed rate `T^{-1/3}`; `η_t = η₀t^{-2/3}` with `0 < η₀ < 1/4` (:133); i.i.d. sampling with
full-support `μ` (:51–67); the asynchronous TD update (:72); the Polyak–Ruppert average (:82); every `V₀`; `d = S`.
`Γ_true ≻ 0` is assumed, since the printed coefficient uses `‖Γ⁻¹‖` and `κ(Γ)`. `lawProb` is the exact i.i.d. law of
`√TΔ̄_T`. `gaussCov (tdA M π μ) (trueGamma M π μ)` is `N(0, A⁻¹ΓA⁻ᵀ)` with `A = diag(μ)(I − γP_π)` (:106–117).
Not implied:
* the convex-distance bound over all convex sets, which remains open;
* the printed coefficient;
* any confidence region or interval, in particular with the estimated covariance `Λ̂_T`
  (SOURCE-ISSUES C47(1)–(4)). -/
def Thm7_11_corrected_halfspace : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K : ℝ, 0 < K ∧
    ∀ T : ℕ, 1 ≤ T → ∀ (u : State → ℝ) (b : ℝ),
      |lawProb M π μ η₀ V₀ T {x | ∑ s, u s * x s ≤ b} -
        (gaussCov (tdA M π μ) (trueGamma M π μ)).real {x | ∑ s, u s * x s ≤ b}| ≤
        K * (T : ℝ) ^ (-(1 / 3 : ℝ))
```

The docstring-before-`open … in` order must match the file's existing style. In my scratch file, a `/--` docstring
placed *before* `open … in theorem` failed to parse. Put the docstring after `open … in`, as the draft does, or use
`open` at section level.

### Wrapper (`Formalization/Statements/Ch7Proofs.lean`; import `Formalization.Ch7Rest.TDInferenceHalfSpace711`)

```lean
open StatisticalRL.Ch7Rest.TDInference in
theorem Thm7_11_corrected_halfspace_holds : Thm7_11_corrected_halfspace := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  exact abs_lawProb_halfSpace_sub_gaussCov_le M π μ h0 (by linarith) V₀ hμ hΓ
```

### COVERAGE row, Theorem 7.11: status lead

Add `TDInferenceHalfSpace711.lean`, `Ch7.lean` and `Ch7Proofs.lean` to the evidence column. Replace the lead with:

> **Printed statement refuted; corrected variant proved on closed half-spaces only.** Under the reading with
> action-dependent rewards and r(s) = r_π(s) in Γ, the printed convex-distance bound is false (…existing refutation
> text unchanged…).
>
> Proved (entry `Thm7_11_corrected_halfspace`, export `abs_lawProb_halfSpace_sub_gaussCov_le`): with the true noise
> covariance Γ_true (assumed ≻ 0), the printed step sizes η_t = η₀t^(-2/3), 0 < η₀ < 1/4, full-support i.i.d.
> sampling and every V₀, there is K > 0 such that for all T ≥ 1 and every closed half-space H = {x : uᵀx ≤ b},
> |P(√TΔ̄_T ∈ H) − N(0, A⁻¹Γ_trueA⁻ᵀ)(H)| ≤ K·T^(-1/3).
> - This is the printed rate, but restricted to half-spaces (1-D projections).
> - K depends on the instance, η₀ and V₀; the printed coefficient is not established.
> - The all-convex corrected statement and the printed coefficient remain open.
> - It implies no convex confidence-region guarantee beyond half-spaces (no ellipsoids or rectangles), and no
>   confidence statement with the estimated covariance (C47).
> - With state-only rewards, Γ_true equals the printed Γ.
>
> Not author-approved. (…keep the groundwork and smooth-partial sentences…)

### SOURCE-ISSUES C43 addendum

> **Half-space result (2026-11-09, `Formalization/Ch7Rest/TDInferenceHalfSpace711.lean`, entry
> `Thm7_11_corrected_halfspace`).** The corrected statement is machine-checked on closed half-spaces at the printed
> rate. With Γ replaced by the true residual covariance Γ_true ≻ 0, for every full-support μ, 0 < η₀ ≤ 1 (the entry
> states the printed 0 < η₀ < 1/4) and every V₀, there is an instance-, η₀- and V₀-dependent K with
> sup_{u,b} |P(uᵀ√TΔ̄_T ≤ b) − N(0, A⁻¹Γ_trueA⁻ᵀ)(uᵀx ≤ b)| ≤ K·T^(-1/3) for all T ≥ 1.
>
> The proof does not use the cited paper. It uses:
> - Chen–Shao nonlinear Stein bound;
> - leave-one-out TD estimates;
> - a Gaussian variance comparison.
>
> It therefore does not depend on the unverified stationarity and estimator differences noted in the scope note.
> Still open:
> - the convex-distance bound over all convex sets;
> - the printed coefficient and the polynomial C̃;
> - the state-only-reward reading of the printed statement (Γ_true = Γ_printed there, so the half-space result is a
>   restricted case of it under that reading).
>
> Independently critic-reviewed (`critic-thm7-11-m9.md`). Not author-approved.

Also fix "full-support μ (`inference.tex:64`)" to `:67` in the scope note.

### Ledger record (`docs/named-result-status.json`, `proved_variants`)

- `name`: "Theorem 7.11 (corrected covariance, closed half-spaces)"
- `source_label`: `thm:Berry-Esseen-linear`
- `source_file`: `chapters/inference.tex`
- `source_lines`: "132–141"
- `source_context_lines`: "47–129 (sampling, TD update, averaging, A, Γ, convex distance)"
- `lean_export`: `StatisticalRL.Ch7Rest.TDInference.abs_lawProb_halfSpace_sub_gaussCov_le`
- `lean_statement`: `…Statements.Ch7.Thm7_11_corrected_halfspace`, with `_holds` as the proof
- `statement_scope`: "Corrected and restricted: true noise covariance Γ_true ≻ 0 instead of the printed Γ (C43,
  printed refuted under the action-dependent-reward reading); closed half-spaces only, not all convex sets; printed
  rate T^(-1/3) with an instance-, η₀- and V₀-dependent constant, printed coefficient not established. Implies no
  convex confidence-region guarantee beyond half-spaces (C47). Not author-approved; this does not certify the
  printed theorem."
- `evidence`: the published copy of this review

### Site (R5)

`CHIP_OVERRIDES["Thm7_11_corrected_halfspace"] = "Proved in corrected form for closed half-spaces only (not all
convex sets; instance constant)"`, plus a `CARD_NOTES` entry repeating the "Not implied" list.
