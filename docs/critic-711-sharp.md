# CRITIC: corrected Theorem 7.11 over all convex sets at T^{-1/3} (end-to-end, statement audit)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent end-to-end review and five-bin statement audit of the corrected Theorem 7.11 over all convex sets at T^(-1/3) (export `abs_lawProb_convex_sub_gaussCov_le_third_sharp`, entry `Thm7_11_corrected`). Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT-WITH-FIXES; five-bin audit PASS-DISCLOSED. The entry and wrapper landed as drafted in section (3). Finding 2: N3 and N4 were reviewed in [critic-nolog-N3N4.md](critic-nolog-N3N4.md) (both ACCEPT), which also checks every upstream signature N4 uses, including the revised `TDInferenceLooVector711.lean` exports; the N1 change since its review is the applied docstring fix of [critic-nolog-N1N2.md](critic-nolog-N1N2.md) finding 1. Finding 3 applied (imports in `Formalization.lean` and `Statements/Ch7Proofs.lean`). Finding 4 applied: the half-space docstring now says it is implied by `Thm7_11_corrected` (entry kept), and COVERAGE, the named-result record (now `Thm7_11_corrected`, no `statement_variant`), SOURCE-ISSUES C43 and ERRATA item 21 use the replacement text of section (4); the oracle confidence-region corollaries keep their proved T^(-1/3)·log(2T) rate and are not re-derived (optional item). Findings 5–6 are notes.

Date 2026-11-10. Independent critic (built none of this). Read-only except its own report and local probes.
Target: `StatisticalRL.Ch7Rest.TDInference.abs_lawProb_convex_sub_gaussCov_le_third_sharp`,
`Formalization/Ch7Rest/TDInferenceConvexSharp711.lean` (sha256 b3a0201a…65bd, 334 lines).
Source read: `source/upstream/tex/chapters/inference.tex:47–141` (sampling :51–67, update :70–75, average :80–83,
Δ̄_T :86–88, Λ⋆/A/Γ :99–117, d_cvx :121–127, theorem :132–141); `prelim.tex:42` (r ∈ [0,1]).

## Verdict: ACCEPT-WITH-FIXES
Mathematics and statement accepted; fixes are process/integration and stale prose.

## (1) Independent reconstruction of the printed theorem
For a discounted MDP (S,A,P,r∈[0,1],γ<1), fixed π, any μ with λ₀ = min μ > 0; i.i.d. tuples s_t∼μ, a_t∼π(·|s_t),
r_t = r(s_t,a_t), s'_t∼P(·|s_t,a_t), t = 1..T; asynchronous TD V_t(s_t) = (1−η_t)V_{t−1}(s_t) + η_t(r_t + γV_{t−1}(s'_t)),
η_t = η₀t^{-2/3}, 0<η₀<1/4; V̄_T = T⁻¹∑_{t=1}^T V_t; V₀ unspecified (read: every V₀). Claim:
sup_{A convex ⊆ ℝ^S} |P(√T(V̄_T−V^π) ∈ A) − N(0, A⁻¹ΓA⁻ᵀ)(A)| ≤ c·[√(η₀/((1−γ)λ₀))TrΓ‖Γ⁻¹‖ + √(Sκ(Γ))/((1−γ)λ₀η₀)]T^{-1/3} + C̃T^{-1/2},
c universal ("≲"), C̃ instance-dependent, T-free; A = diag(μ)(I−γP_π); Γ diagonal (needs Γ ≻ 0 for ‖Γ⁻¹‖, κ).

Comparison with the export (definitions in `TDInference711Defs.lean` read in full for the used objects):
- `tupleProb` = μ(s)π(a|s)P(s'|s,a), `pathWeight` = product: exact i.i.d. law. `tdStep` updates only s_t with r(s,a)+γV(s');
  `tdIter` uses `stepSize η₀ (t+1)` for V_{t+1} (η_t = η₀t^{-2/3}, t ≥ 1, no 0^{-2/3} junk). `prAverage` = T⁻¹∑_{t=1}^T V_t.
  `scaledError` = √T(V̄_T − V^π). `lawProb` = exact P(√TΔ̄_T ∈ C) for any set C (finite sum). Match.
- `gaussCov A Γ` = law of A⁻¹(√Γ⊙Z), covariance A⁻¹diag(Γ)A⁻ᵀ; `tdA` = diag(μ)(I−γP_π), invertible under μ>0, γ<1
  (no junk inverse). With Γ := `trueGamma` (C43 correction). Match up to the disclosed covariance change.
- All convex C, measurable or not; Gaussian side `.real` = outer measure (same reading as `Eq_convex_distance_le_TV`).
  ∀C inside ⇔ sup bound (values in [0,1], no junk iSup). Match.
- Quantifiers: instance, η₀, V₀ → ∃K>0 → ∀T≥1 → ∀C. K before T and C. K depends on instance, η₀, V₀ (disclosed).
- η₀ ≤ 1 in the export vs printed <1/4: export assumes less; the entry states the printed range. Fine.
- Γ_true ≻ 0: analogue of the printed definedness of ‖Γ⁻¹‖, κ(Γ); proposed in C43 ("with Γ ≻ 0 assumed"). Used
  (reservoir λ lower bound) and not droppable in general: in the C43 zero-noise instance Γ_true = 0, the Gaussian is δ₀,
  and from V₀ ≠ V^π the statistic is nonzero, so the distance at {0} is not small (paper argument). DISCLOSED.
- Printed coefficient/C̃: not established; K is an instance constant (and C̃T^{-1/2} ≤ C̃T^{-1/3} absorbed). DISCLOSED.

## (2) Dependency chain (statement level)
N4 main = small-T trivial bound (`abs_sum_pathWeight_indicator_sub_gaussCov_le_one`, N^{1/3}T^{-1/3} ≥ 1) +, for T ≥ N,
triangle inequality of
(a) linear part `abs_linLaw_convex_sub_gaussCov_le_third_of_burnIn` (ConvexLinSharp711; reviewed critic-allconvex-m5b2-a/b,
third-log) and (b) nonlinear transfer `abs_lawProb_sub_linLaw_le_third_of_burnIn` (N4), which instantiates N3
`Stein.Polyhedral.abs_pexp_convex_add_sub_le_update` with every hypothesis discharged in the file: hp0/hp1 (tupleProb),
hmean (`sum_tupleProb_mul_linSummand`), hbd (`norm_linSummand_le_inv_sqrt`), λ (`linSummand_quad_lower` via
`exists_linFactor_reservoirCond_of_pos`, ConvexReservoir711, reviewed m5a2/m6a/m7/m8a3), and the moment inputs
(`pexp_norm_vsum_le`, `pexp_devSum_le`, `sum_pathWeight_mul_norm_linPart_mul_le`, `sum_looChenShao_abs_norm_sub_le`).
N3 is a theorem with only the listed premises (read at ConvexNonlinearTransfer.lean:217–232); N1/N2 reviewed
([critic-nolog-N1N2.md](critic-nolog-N1N2.md)). No hypothesis is left undischarged: the main export's type has exactly the premises listed above.
Axioms (compiled `<local probe>` (draft entry and wrapper), `bash scripts/lean-local.sh`, rc 0, oleans newer than sources):
main export and draft `_holds` → [propext, Classical.choice, Quot.sound].

## (3) Draft entry (compiled: the draft statement probe imports only TDInference711Defs, rc 0; the draft proofs probe rc 0,
including an `example` deriving `Thm7_11_corrected_halfspace`'s Prop from it via `convex_halfSpace_le`)

```lean
section Thm7_11 -- in Formalization/Statements/Ch7.lean, before Thm7_11_corrected_halfspace

open StatisticalRL StatisticalRL.Ch7Rest.TDInference in
/-- Theorem 7.11 (`thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`; convex distance
`eqn:convex-distance` :124–127; `Λ⋆` :104–117), corrected covariance, all convex sets, instance constant.
Differs from the printed result in two ways.
(1) `Γ` is the true per-sample TD-noise covariance `trueGamma`,
`Γ_ss = μ(s) E_{a∼π(·|s), s'∼P(·|s,a)}[(V^π(s) − r(s,a) − γV^π(s'))²]`, so the Gaussian is
`N(0, Λ)` with `Λ = A⁻¹ diag(Γ_true) A⁻ᵀ`, `A = diag(μ)(I − γP_π)`. The printed `Γ` (:115) averages only over
`s' ∼ P_π` with an undefined `r(s)`; read as `r_π(s)` it omits the action-reward variance and the cross term
`2γCov(r(s,a), V^π(s'))`, and the printed theorem is then false (SOURCE-ISSUES C43). With state-only rewards
(or deterministic `π`) the two coincide.
(2) The `T^{-1/3}` constant `K` depends on the instance, `η₀` and `V₀`. It is not shown to be a universal multiple of
the printed `√(η₀/((1−γ)λ₀))Tr Γ‖Γ⁻¹‖ + √(Sκ(Γ))/((1−γ)λ₀η₀)`, and `C̃T^{-1/2}` is absorbed into `K`, so it is not
shown polynomial.
Kept: the printed rate `T^{-1/3}`; `d_cvx` over all convex `C ⊆ ℝ^S` (written as a bound for every convex `C`;
non-measurable `C` allowed, the Gaussian side being the outer measure); `η_t = η₀t^{-2/3}` with `0 < η₀ < 1/4` (:133);
i.i.d. sampling with full-support `μ` (:51–67); the asynchronous TD update (:72); the Polyak–Ruppert average (:82);
every `V₀`; `d = S`. `Γ_true ≻ 0` is assumed, the corrected analogue of the printed `‖Γ⁻¹‖`, `κ(Γ)` being finite.
`lawProb` is the exact i.i.d. law of `√TΔ̄_T`; `gaussCov (tdA M π μ) (trueGamma M π μ)` is `N(0, Λ)`.
Our own proof (randomized concentration for polyhedral representations of convex sets plus leave-one-out TD
estimates), not the cited paper's. Implies `Thm7_11_corrected_halfspace`.
Not implied: the printed coefficient; the printed statement under the state-only-reward reading; any confidence
region with the estimated covariance `Λ̂_T` (SOURCE-ISSUES C47). -/
def Thm7_11_corrected : Prop :=
  ∀ (State Action : Type) [Fintype State] [DecidableEq State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ),
    (∀ s, 0 < μ.prob s) → 0 < η₀ → η₀ < 1 / 4 → (∀ s, 0 < trueGamma M π μ s) →
    ∃ K : ℝ, 0 < K ∧
    ∀ T : ℕ, 1 ≤ T → ∀ C : Set (State → ℝ), Convex ℝ C →
      |lawProb M π μ η₀ V₀ T C - (gaussCov (tdA M π μ) (trueGamma M π μ)).real C| ≤
        K * (T : ℝ) ^ (-(1 / 3 : ℝ))
```

Ch7Proofs.lean (needs `import Formalization.Ch7Rest.TDInferenceConvexSharp711`):

```lean
/-- `Thm7_11_corrected` from
`StatisticalRL.Ch7Rest.TDInference.abs_lawProb_convex_sub_gaussCov_le_third_sharp`
(the export needs only `η₀ ≤ 1`). -/
theorem Thm7_11_corrected_holds : Thm7_11_corrected := by
  intro State Action _ _ _ _ _ M π μ η₀ V₀ hμ h0 h1 hΓ
  exact StatisticalRL.Ch7Rest.TDInference.abs_lawProb_convex_sub_gaussCov_le_third_sharp M π μ h0
    (by linarith) V₀ hμ hΓ
```
Wrapper applies the library export only (η₀<1/4 ⇒ η₀≤1). Import gate: only `TDInference711Defs` (allowed by g2).

### Five-bin audit of `Thm7_11_corrected`
| binder | Lean type | bin | citation |
|---|---|---|---|
| State, Action | Type | TYPING | finite tabular MDP |
| [Fintype State], [Fintype Action], [DecidableEq State] | instances | TYPING | |
| [Nonempty State], [Nonempty Action] | instances | TYPING | redundant with M fields |
| M | DiscountedMDP (γ∈[0,1), r∈[0,1], P) | STANDING | inference.tex:48, prelim.tex:42 |
| π | StationaryPolicy | SOURCE | :48 |
| μ | FiniteDistribution | SOURCE | :67 |
| η₀ | ℝ | SOURCE | :133 |
| V₀ | State → ℝ (∀) | SOURCE (implicit, strongest reading) | :70–75 |
| ∀ s, 0 < μ s | hyp | SOURCE | :67 λ₀>0 |
| 0 < η₀, η₀ < 1/4 | hyp | SOURCE | :133 |
| ∀ s, 0 < trueGamma s | hyp | DISCLOSED | C43 (Γ ≻ 0 assumed); definedness of ‖Γ⁻¹‖,κ |
| covariance trueGamma in gaussCov | conclusion object | DISCLOSED | C43 |
| ∃K (instance, η₀, V₀) before ∀T | quantifier | DISCLOSED | docstring (2), C43 |
| T : ℕ, 1 ≤ T | | SOURCE | :54 |
| C, Convex ℝ C | | SOURCE | :124–127 (all convex sets, outer-measure reading) |
Counts: SOURCE 8, STANDING 1, TYPING 3 rows, DISCLOSED 3, EXCESS 0. Self-contained (no theorem-type reference);
hypotheses satisfiable (e.g. one-state instance with π uniform on rewards 0,1: Γ_true = 1/4, C47 evidence file);
no junk values (A invertible, Γ_true ≥ 0 under √, T ≥ 1). Verdict: PASS-DISCLOSED (once C43 is updated, finding 5).

Half-space entry: now implied (compiled). Recommend KEEP it (it has an independent proof route and is cited by
`Eq_convex_Cdelta_corrected_oracle`), but edit its docstring: delete "Not implied: the convex-distance bound over all
convex sets (corrected), which remains open" and add "Implied by `Thm7_11_corrected`". Its named-result record should
be replaced by one for `Thm7_11_corrected` (no `statement_variant` field; gen_nodes classifies by the `_corrected` name).

## (4) Proposed replacement text
COVERAGE Theorem 7.11 row, headline and the "Proved" sentence:
> **Printed statement refuted; corrected variant proved over all convex sets at the printed rate (instance constant).**
> … Proved (entry `Thm7_11_corrected`, export `abs_lawProb_convex_sub_gaussCov_le_third_sharp`,
> [TDInferenceConvexSharp711.lean](../Formalization/Ch7Rest/TDInferenceConvexSharp711.lean)): with the true noise covariance
> Γ_true (assumed ≻ 0), η_t = η₀t^(-2/3), 0 < η₀ < 1/4, full-support i.i.d. sampling and every V₀, there is K > 0 such
> that for all T ≥ 1 and every convex C ⊆ ℝ^S, |P(√TΔ̄_T ∈ C) − N(0, A⁻¹Γ_trueA⁻ᵀ)(C)| ≤ K·T^(-1/3). K depends on the
> instance, η₀ and V₀; the printed coefficient and the polynomial C̃ are not established. Our own proof (randomized
> concentration for polyhedral representations of convex sets, leave-one-out TD estimates, reservoir Lindeberg linear
> part), not the cited paper's. The half-space entry `Thm7_11_corrected_halfspace` is a corollary (also proved separately).
> Not refuted and not proved: the printed statement under the state-only-reward reading (where Γ_true = Γ).
Delete "The all-convex corrected statement … remain open" and "Theorem 7.11 over all convex sets at the printed rate
(without the logarithm) remains open"; relabel the T^(-1/3)·log(2T) and T^(-1/4), T^(-2/9) results as earlier, weaker bounds.

named-result-status.json record:
- name "Theorem 7.11 (corrected covariance, all convex sets)"; lean_export `…abs_lawProb_convex_sub_gaussCov_le_third_sharp`;
  lean_statement `…Thm7_11_corrected`; proof `…Thm7_11_corrected_holds`; remove `"statement_variant": "restricted"`.
- statement_scope: "Corrected: true noise covariance Γ_true ≻ 0 instead of the printed Γ (C43; the printed theorem is
  refuted under the action-dependent-reward reading, and neither proved nor refuted under the state-only-reward
  reading). Over all convex sets at the printed rate T^(-1/3), for every V₀ and 0 < η₀ < 1/4, with an instance-, η₀- and
  V₀-dependent constant; the printed coefficient and C̃ are not established. Own proof, not the cited paper's. Implies
  no confidence region with the estimated covariance (C47). Not author-approved; this does not prove the printed theorem."
- evidence: this review once published as docs/critic-711-sharp.md; supporting: N1N2, nolog-infra, allconvex-m5b2-a/b, third-log,
  and the missing N3/N4 reviews (finding 2).

C43: replace "Still open: the convex-distance bound over all convex sets; the printed coefficient …" (half-space
paragraph) and "The corrected statement … including its convex-set bound, remains open" (scope note) by a new paragraph:
> **All convex sets (2026-11-10, `Formalization/Ch7Rest/TDInferenceConvexSharp711.lean`, entry `Thm7_11_corrected`).**
> The corrected statement is machine-checked over all convex sets at the printed rate: with Γ_true ≻ 0, full-support μ,
> 0 < η₀ ≤ 1 (the entry states 0 < η₀ < 1/4) and every V₀, there is an instance-, η₀- and V₀-dependent K with
> sup_{C convex} |P(√TΔ̄_T ∈ C) − N(0, A⁻¹Γ_trueA⁻ᵀ)(C)| ≤ K·T^(-1/3) for all T ≥ 1 (outer measure for non-Borel C).
> Our own proof (randomized concentration over polyhedral representations of convex sets plus leave-one-out TD
> estimates); it does not use the cited paper, so the unverified stationarity/estimator differences do not affect it.
> Still open: the printed coefficient and polynomial C̃; the printed statement under the state-only-reward reading.
> The printed statement remains refuted under the action-dependent-reward reading. Not author-approved.

## Findings
1. (accept) Export statement matches the corrected printed theorem; all deviations disclosed; axioms clean.
2. (fix, process) No critic report exists for N3 `ConvexNonlinearTransfer.lean` (sha 75ffbbd9…) or N4 beyond this one
   (only local compile logs). `TDInferenceLooVector711.lean` changed since critic-nolog-infra (8a6aa3f… →
   bc800cbb…); the exports N4 uses (`norm_linSummand_le_inv_sqrt`, `sum_pathWeight_mul_norm_linPart_mul_le`,
   `sum_looChenShao_abs_norm_sub_le`) are unreviewed. N1 changed since the N1N2 review (750a0a65… → 2cb73853…). Soundness is
   Lean-checked; docstring/infrastructure honesty review of these still needed before integration.
3. (fix, integration) N3/N4 not imported by `Formalization.lean`, so `Audit.lean`/check.py do not yet cover them; add
   `import Formalization.Ch7Rest.TDInferenceConvexSharp711` and the Ch7Proofs import.
4. (fix) Stale "all-convex remains open" text: half-space entry docstring, COVERAGE row (and C∆ row's "the rate without
   log(2T)" open item, now reachable by rerouting the oracle-region corollaries — optional), named-result scope, C43.
5. (note) `Nonempty Action` binder redundant (M field); harmless, mirrors half-space entry.
6. (note) K also absorbs the small-T burn-in N^{1/3}; fine for an instance constant.
