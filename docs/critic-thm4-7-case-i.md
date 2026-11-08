# CRITIC: Theorem 4.7 case (i) and the combined printed Theorem 4.7

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this review covered the builder's pre-integration snapshot. The seven library modules were integrated unchanged except for their imports, as `Formalization/ModelFree/QLearningLowerBoundRescaledRates.lean` (Rates), `Formalization/ModelFree/QLearningLowerBoundVaryingDefinitions.lean` (VaryingDefinitions), `Formalization/ModelFree/QLearningLowerBoundVaryingPathwise.lean` (VaryingPathwise), `Formalization/ModelFree/QLearningLowerBoundVaryingState2.lean` (VaryingState2), `Formalization/ModelFree/QLearningLowerBoundVaryingMoments.lean` (VaryingMoments), `Formalization/ModelFree/QLearningLowerBoundVaryingOverestimation.lean` (VaryingOverestimation) and `Formalization/ModelFree/QLearningLowerBoundRescaledTheorem.lean` (RescaledTheorem). The combining step of the draft wrapper `Thm4_7_of_case_i` (StatementImplies) was added at the end of `QLearningLowerBoundRescaledTheorem.lean` as the library theorem `qLb_thm47`, with the same `max`/`min` combination of constants and the statement text of `Thm4_7`, so that the wrapper `Thm4_7_holds` applies a library theorem; `Thm4_7_of_case_i` itself was not integrated. The statement files became the entries `Thm4_7` and `Thm4_7_case_i` in `Formalization/Statements/Ch4.lean`, with the wrappers `Thm4_7_holds` and `Thm4_7_case_i_holds` in `Formalization/Statements/Ch4Proofs.lean`. On integration the `Thm4_7` docstring was changed to address F1 (explicit constants c₃ = 16 and c_lb = 10⁻⁹; the sentence with the sum was removed) and F4 (the proof description was replaced by a pointer to the library module), and the `Thm4_7_restricted` docstring was rewritten as "implied by `Thm4_7`; retained for history" (R1). The ledger records Theorem 4.7 as the certified printed result `Thm4_7` (its `proved_variants` record for case (ii) was removed, R1/R2), and C30 is marked resolved. Short module names below refer to these integrated files; the file hashes quoted below are those of the reviewed snapshot. The review text below is otherwise unchanged.

Independent critic, 2026-11-08. I did not write any builder file and edited none.

## Pins

| Item | Value |
|---|---|
| HEAD | `58bb234219e157a6d4cec61b9786caf6b0eefb4d` |
| Source `chapters/generative_model_model_free.tex` | sha256 `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22` (`thm:LB-example-Q-generative` at `:969–982`; Appendix C scope sentence at `:2711`; `alg:q-infinite` at `:836–862`) |
| The builder's reviewed snapshot (10 files) | All 10 files match the builder's snapshot hash list (sha256 `5041946c…b713`). The builder's live working files are byte-identical to the snapshot. |
| Plan / check | builder's private plan `9dbb17a3…bbb`; plan check `78a4165f…110` (hash of the private original; public copy `critic-thm4-7-case-i-plan-check.md`) |
| Probe | `CriticProbe.lean` (reviewer's private probe folder) `dd9a3b8a…ba4c`, output `critic-probe.out` `1ba2c057…40ba` |

## Independent rebuild

I copied the snapshot to the reviewer's private probe folder, renaming only the module prefix
(builder's working prefix → reviewer's private prefix). I then compiled it sequentially, in the foreground, with
`bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean <file>`, in the order
Statement, StatementImplies, Rates, VaryingDefinitions, VaryingPathwise, VaryingState2,
VaryingMoments, VaryingOverestimation, RescaledTheorem, StatementProof.

- Every module exited 0, and the combined output had 0 lines: no errors, no warnings and no
  `declaration uses 'sorry'`.
- A grep of the snapshot for `sorry|admit|axiom |native_decide|implemented_by|extern|unsafe|opaque|macro_rules`
  and for `set_option` found nothing.

## Axioms (re-probed on the critic rebuild)

`#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for each of:

- `Thm4_7_holds`
- `Thm4_7_case_i_holds`
- `Thm4_7_of_case_i`
- `qLb_thm47_rescaledLinear`
- `qLbv_caseAB`
- `qLbv_caseC`
- `qLbv_xiMax_lower`
- `qLbv_state2_mean`

This agrees with the builder's `axiom-probe.out`. The `static_gates.py` check was skipped because it does not apply to WIP.

## 1. Statement fidelity (`#print`-verified elaborated forms)

| Printed (`:969–982`) | `Thm4_7` / `Thm4_7_case_i` | Verdict |
|---|---|---|
| "for some sufficiently large constant `c₃>0`", "some universal constant `c_lb>0`" | `∃ c₃ c_lb, 0<c₃ ∧ 0<c_lb ∧ ∀ γ …` | ✓ The constants come first and are independent of γ, T, c_η and η₀. The ∃-reading of "sufficiently large" is equivalent to the threshold reading, because the hypothesis `c₃/(1−γ)² ≤ T` is monotone in c₃. |
| `3/4 ≤ γ < 1` | `3/4 ≤ γ → γ < 1` | ✓ |
| `T ≥ c₃/(1−γ)²` | `T : ℕ`, `c₃/(1−γ)² ≤ ↑T` | ✓ |
| `Q₀ ≡ 0` | `(fun _ _ ↦ 0)` | ✓ |
| (i) `η_t = 1/(1+c_η(1−γ)t)` for any constant `c_η>0`, for all `t≥0` | `∃ cη, 0<cη ∧ ∀ t:ℕ, η t = 1/(1+cη(1−γ)t)` (combined); `∀ cη, 0<cη →` with the schedule inlined (case (i)) | ✓ `c_lb` does not depend on `c_η`, which is the strong, literal reading. `η 0 = 1` is never used, because round `t+1` of `qLearningIterate` uses `η (t+1)`, as in `alg:q-infinite` (`Q_t = (1−η_t)Q_{t−1} + η_t 𝒯_t(Q_{t−1})`, `t=1..T`). |
| (ii) `η_t ≡ η ∈ (0,1)` for all `t≥0` | `∃ η₀, 0<η₀ ∧ η₀<1 ∧ ∀ t, η t = η₀` | ✓ Identical in content to `Thm4_7_restricted`'s `∀ η, 0<η → η<1` with `fun _ ↦ η` (both directions were checked in the probe; see below). |
| ∃ γ-discounted MDP with S=4, A=2 | `∃ M : DiscountedMDP (Fin 4) Bool, M.discount = γ` | ✓ Rewards in [0,1] and probability rows are structure fields. The source uses state-dependent action sets, padded with dominated dummy actions (C31(5)), which is disclosed. |
| `max_s E|V_T(s)−V⋆(s)|² ≥ c_lb/((1−γ)⁴ T log² T)` | `∃ s, c_lb/((1−γ)^4 * T * Real.log T ^ 2) ≤ ∫ (qLearningValue M Q_T s − V⋆ s)^2 ∂qSamplingLaw M T` | ✓ `∃ s` is equivalent to the max over a finite set. `Real.log T ^ 2` elaborates as `(log T)²`. The natural log is disclosed. |

**Schedule binder.** The disjunction is neither vacuous nor ambiguous. The probe proves that no
rescaled schedule equals a constant `η₀ < 1`, since at `t=0` the rescaled schedule gives 1. Both
disjuncts are inhabited, and the probe derives `Thm4_7 → Thm4_7_case_i` and `Thm4_7 → Thm4_7_restricted`.

**MDP order of quantifiers.** In the Lean statements, M is chosen after γ, T and the schedule, so
M may depend on `c_η`. This is the literal reading of the printed sentence order ("Suppose … learning
rates … There exists an MDP"). The proof's witness is `qLbMDP γ` in every case, so it depends only on
γ, which is stronger than stated. Allowed. If the lead wants the stronger uniform-M form to be
visible, that would be a separate library statement (F3).

**Expectation is genuine.**
- `qSamplingLaw M T` is the product law of the transition rows (`ModelBasedPolicyLearning.samplingLaw`).
  The probe shows `IsProbabilityMeasure` by `inferInstance`.
- The sample space is finite, and `qSampling_integrable` is `Integrable.of_finite`.
- The lower bound is strictly positive whenever T ≥ 2. The probe instantiates γ = 3/4,
  T = ⌈16c₃⌉₊+2 and c_η = 1, using the export's own c₃. So a junk value of 0 for the integral would
  make the statement false, not trivially true.
- `qSampledIterate` is `qLearningIterate` on `qSamplesExtend`: the zero-indexed draw `t−1` is used at
  round t, and the out-of-range default is never queried for t ≤ T.
- `V⋆` is `M.trajectoryExpectedValue M.optimalGreedyPolicy`. For the witness it equals
  `qHardValue γ`, that is (0, 3/(4(1−γ)), 3/(4(1−γ)), 1/(1−γ)) (`qLbMDP_value`, `qLb_vstar_eq`),
  which matches the source's V⋆ of M_hard.

**Non-vacuity.** The probe's first `example` compiles. With γ = 3/4, T = ⌈16c₃⌉₊+2 ≥ 2 and
c_η = 1, the theorem yields an M with discount 3/4 and an s such that
`0 < c_lb/((1/4)^4 T log²T) ≤ E[(V_T(s)−V⋆(s))²]`.

## 2. Mathematics: meaning of the key lemma statements

- `qLbv_pathwise` (for all t ≤ N, along a valid stream) states:
  - `Q_t(0,·)=0` and the dummy entries are 0;
  - `Q_t(3,false) = (1−Π_{1−γ}(0,t))/(1−γ)`;
  - `Q_t(2,false)` equals the chain `v_t`;
  - `Q_t(1,a) ≥ Q̂_t(a) − Π_{1−γ}(0,t)/(1−γ)`.

  Its only hypothesis is `0 ≤ η ≤ 1`. This is the time-varying form of Step 2 and of
  `eq:Qt-lower-bound-generative`. ✓
- `qLbv_output_ae` transfers these facts to the actual experiment a.s., using `qLb_valid_ae`. ✓
- `qLbv_state2_mean` states that `V⋆(2) − E v_t = Π_{1−γp}(0,t)·V⋆(2)` exactly. This is the
  time-varying `eq:EV2`, and it is consumed by `qLbv_state2_bias` (Jensen: squared bias ≤ second moment). ✓
- `qLbv_xiMax_lower` states that `E ξ_{t,max} ≥ (5/1536)·min(√(η̄/(1−γ)),1)` under an abstract `η̄ > 0`
  with `η̄/3 ≤ S₂(t) ≤ η̄` and `S₄(t) ≤ η̄² S₂(t)`. Here S₂ and S₄ are the recursive square and fourth
  power sums of the ξ-weights. These are exactly the recursions of the weights
  `η_k ∏_{j>k}(1−η_j)`, so this is a sound reformulation of fix (3) (deviation 1).
- `qLbv_xiMax_lower_rescaled` discharges those hypotheses for `η_j = 1/(1+Dj)` with 0 ≤ D ≤ 1 and
  1 ≤ t ≤ N, with `η̄ = η_t`. Deviation 1 adds no hypothesis to any export. ✓
- `qLbv_step5` states that `E ξ_{t,max} ≥ b` for 1 ≤ t ≤ N implies
  `γp·b·(1 − Π_{1−γp}(1,N)) ≤ (1−γp)(E V̂_N − V⋆(1))`. This is the repaired Step 5.4 (C31(4)),
  with the `ρ^{T−τ̂}` exponent handled through Π(1,N) instead of the printed closed form. ✓
- `qLbv_caseAB` covers two cases with state 2 and `c_lb = 10⁻⁹`:
  - Case A: `c_η(1−γ) > 1`.
  - Case B: `∑_{t∈(0,T]} (1−γp)η_t ≤ 1/2`.

  The hypotheses are exactly the case split in the export, and they are exhaustive with Case C
  (`lt_or_ge`, `le_or_gt`). ✓
- `qLbv_caseC` covers `c_η(1−γ) ≤ 1` and the sum > 1/2. It derives `c_η < 8 log T` and
  `Π_{1−γp}(1,T) ≤ 6/7`, then combines over-estimation at state 1 with under-estimation at state 3,
  so one of them carries half. The rate factor is `√(η_T/(1−γ))` with
  `η_T ≥ 1/(1+8(1−γ)T log T)`, which gives `≍ 1/((1−γ)⁴ T log T)` and fits the printed `log² T`. ✓
- `qLb_thm47_rescaledLinear` has the same text as `Thm4_7_case_i`, and `Thm4_7_case_i_holds` is
  that export applied directly, by term.

  Deviation 4 (internal `∀ t, 0 ≤ η t ≤ 1`, including t = 0) is discharged inside the proof by
  `qLbvRate_bounds`. The exports carry no η hypothesis. ✓
- `Thm4_7_of_case_i` combines the case (i) and case (ii) exports with `max c₃` and `min c_lb`
  (16 and 10⁻⁹) and does no new mathematics. This is allowed by AGENTS.md: the wrapper derives the
  printed statement from the exports.

**Mathematical sanity.**
- Uniformity in c_η is plausible in every regime.
  - Large c_η: Q-learning barely moves, so the state-2 bias is large.
  - c_η(1−γ) ≤ 1: case C, η_T ≳ 1/((1−γ)T log T).
  - Tiny c_η: η_t ≈ 1 early, and the sum condition puts it in case C with the min(·,1) cap.
- The source never uses the WLOG `log T ≤ 1/(1−γ)` (C31(1)), and the export does not assume it, so
  no hidden restriction remains.

## 3. Ledger implications

- C31 states explicitly: "None of (1)–(5) changes the printed statements of Theorem 4.7 (ii) or
  Lemma 4.15; they change only the unnamed constants". Item (5) is an encoding of the S=4, A=2
  instance, disclosed in the docstring.
- The repairs therefore concern the proof, not the statement. A certified, suffix-free `Thm4_7` is
  honest.
- C30 is resolved: the printed statement is true with c_lb independent of c_η, which settles the
  question C30 left open, and a self-contained formal proof is supplied. The source omission remains a
  recorded fact.

## Verdicts

| Entry | Verdict |
|---|---|
| `Thm4_7` (+ `Thm4_7_holds`, `Thm4_7_of_case_i`) | **ACCEPT WITH DISCLOSURES**. The disclosures are the encoding items already in the docstring: dummy actions (C31(5)), ∃s for the max, the V⋆ convention, natural log, T : ℕ, η 0 unused. They become a plain ACCEPT once R1–R3 are applied at integration. |
| `Thm4_7_case_i` (+ `Thm4_7_case_i_holds`) | **ACCEPT** as a reading-aid entry, implied by `Thm4_7`. It must not get its own ledger record (R2). |
| Library export `qLb_thm47_rescaledLinear` and the `qLbv*` lemmas | **ACCEPT** |

### R-items (required at integration)

- **R1.** Rewrite the `Thm4_7_restricted` docstring.
  - It currently says "Case (i) … remains an open obligation". After integration that is false.
  - Either delete `Thm4_7_restricted` and its `_holds`, or keep it with the docstring changed to
    "Implied by `Thm4_7`; retained for history".
  - Remove its `proved_variants` record in `docs/named-result-status.json` (around `:853–861`).
    Replace it with one `certified_named_results` record for `StatisticalRL.Statements.Ch4.Thm4_7` /
    `Thm4_7_holds`, whose exports are `qLb_thm47_rescaledLinear` and `qLb_thm47_constantRate`, and
    whose evidence is this file.

  Recommendation: keep `Thm4_7_restricted` as a historical, implied entry (the probe shows
  `Thm4_7 → Thm4_7_restricted`), because existing links point at it.
- **R2.** Exactly one ledger record for Theorem 4.7. `Thm4_7_case_i` is not a separate source result,
  so it gets no record and no count (no double counting in `corrected_variant_count` or
  `certified_*`).
- **R3.** Integration hygiene.
  - Final module names under `Formalization/ModelFree/`.
  - `Thm4_7` and `Thm4_7_case_i` go in `Statements/Ch4.lean`, which stays proof-free.
  - `Thm4_7_of_case_i`, `Thm4_7_case_i_holds` and `Thm4_7_holds` go in `Ch4Proofs.lean`.
  - Imports go in `Formalization.lean`, followed by the full `python3 scripts/check.py`, the axiom
    audit, and a re-run of the static gates on the integrated tree.
  - COVERAGE, PROGRESS (ownership, count) and SOURCE-ISSUES C30 are updated in the same change.

### F-items (optional)

- **F1.** In the `Thm4_7` docstring, write `∑_{t ≤ T}` as `∑_{1 ≤ t ≤ T}`, which is what
  `Finset.Ioc 0 T` means. Also record the explicit constants (c₃ = 16, c_lb = 10⁻⁹), as the restricted
  docstring did.
- **F2.** `qLbv_step5`'s docstring says "(and N ≥ 1)". That is fine as written; the hypothesis is `hN`.
- **F3.** Optionally expose the stronger uniform-witness form, with M = `qLbMDP γ` independent of T
  and the schedule, as a library remark. Not required for fidelity.
- **F4.** The `Thm4_7` docstring sentence "the squared bias of state 2 when …" describes the proof,
  not the statement. It is acceptable, but could move to the library module docstring.

## Recommended ledger text

**COVERAGE row (`docs/COVERAGE.md:121`)**

> **Proved** (`Thm4_7`; reading-aid entry `Thm4_7_case_i`). Both printed learning-rate schedules are
> covered: (i) rescaled linear `η_t = 1/(1+c_η(1−γ)t)` for every `c_η > 0`, and (ii) constant
> `η ∈ (0,1)`. The constants are universal: c₃ = 16 and c_lb = 10⁻⁹, independent of c_η and η.
>
> For γ ∈ [3/4,1) and T ≥ c₃/(1−γ)², a 4-state 2-action MDP (`M_hard` with dominated dummy actions,
> [C31](SOURCE-ISSUES.md#C31) item 5) has E[(V_T(s)−V⋆(s))²] ≥ c_lb/((1−γ)⁴T log²T) at some s, under
> the sampling law of `alg:q-infinite` from Q₀ ≡ 0.
>
> - Case (ii) follows Appendix C with the printed-proof slips repaired ([C31](SOURCE-ISSUES.md#C31)).
> - Case (i) is not proved in the monograph, which defers it to li2024q
>   ([C30](SOURCE-ISSUES.md#C30)). Its Lean proof is self-contained: state-2 bias, plus time-varying
>   over-estimation at states 1 and 3.
>
> `Thm4_7_restricted` (case (ii)) is implied and retained for history. Independently source-reviewed
> (this review, `docs/critic-thm4-7-case-i.md`). Not author-approved.

**C30 (`docs/SOURCE-ISSUES.md`)**: append a resolution paragraph and keep the candidate:

> **Resolved (2026-11-08).** The source omits the argument for case (i) and defers it to li2024q.
> The printed statement is true as printed, with `c_lb` independent of `c_η`. The universal constants
> are c₃ = 16 and c_lb = 10⁻⁹.
>
> The formal proof is new and self-contained (`qLb_thm47_rescaledLinear`):
> - if `c_η(1−γ) > 1` or `∑_{1≤t≤T}(1−γp)η_t ≤ 1/2`, the squared bias of state 2 suffices;
> - otherwise, `c_η < 8 log T`, and time-varying over-estimation at state 1 is combined with
>   under-estimation at state 3.
>
> Together with case (ii) it gives the suffix-free entry `Thm4_7`. The "Formal entry" line is
> replaced by `Thm4_7`; `Thm4_7_restricted` is implied.

## Probe file contents (summary)

`CriticProbe.lean` (reviewer's private probe folder) compiles with exit 0 and contains:

- `#print` of both Props;
- the axiom prints;
- the non-vacuity instantiation;
- the exclusivity of the schedule disjuncts;
- `Thm4_7 → Thm4_7_restricted` and `Thm4_7 → Thm4_7_case_i`;
- the V⋆ identification checks;
- `IsProbabilityMeasure (qSamplingLaw M T)`.

Critic oleans are in the reviewer's private olean folder and are probe-only artifacts. Delete
them before release.
