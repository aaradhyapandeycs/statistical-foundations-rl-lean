# CRITIC: trivial batch C (Ch2–5), independent review

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this critic reviewed the pre-integration snapshot; the nine entries were integrated into the library on 2026-11-08. R1 was applied before landing: the `Thm3_9` and `Thm3_9_positiveN` docstrings, the Theorem 3.9 row of `COVERAGE.md`, the Theorem 3.9 ledger `statement_scope` in `named-result-status.json`, and the Theorem 3.9 bullet of `SOURCE-ISSUES.md#statement-index-scope-disclosures` all state that S, A, H ≥ 1 are forced and that the entry is never vacuous. Snapshot files map to the integrated locations as follows: `IterationCount.lean` → `Formalization/MDP/IterationCount.lean`; `MatrixBellman.lean` → `Formalization/MDP/MatrixBellman.lean`; `PolicyEvaluationCrude.lean` → `Formalization/Generative/PolicyEvaluationCrude.lean`; `QLearningRateFacts.lean` → `Formalization/ModelFree/QLearningRateFacts.lean`; `GreedyValueIdentity.lean` → `Formalization/Online/SourceOptimism/GreedyValueIdentity.lean`; `ChNStmt.lean` → the entries in `Formalization/Statements/ChN.lean`; `ChNPrf.lean` (written `ChNPrf` below, e.g. `Ch3Prf`) → the `_holds` wrappers in `Formalization/Statements/ChNProofs.lean` (N = 2, 3, 4, 5). `CHECK` items (C4-a, C5-a, C7-a, C7-b, X1, placement) refer to the independent plan check, published as `critic-trivial-batch-plan-check.md`. Short file names below refer to the reviewed snapshot files, and the file hashes are those of the snapshot. The review text below is otherwise unchanged.

Status: COMPLETE. Overall: all nine entries ACCEPT or ACCEPT WITH DISCLOSURES; one required text fix (R1, Thm 3.9 docstring/ledger wording). No REJECT.

Target: the builder's read-only pre-integration snapshot (13 Lean files, private working copy).
Snapshot hashes verified against the builder's snapshot hash list (all 13 OK); the builder's live working files identical (all 13 OK).

## Early observations

- O1 (stale builder oleans): `Ch2Stmt.lean` (mtime 21:08:32) and `Ch3Stmt.lean` (mtime 21:11:02) were edited
  after their last successful olean (21:08:07, 21:10:40). The builder's `axiom-probe.out` therefore does not
  certify the snapshot text of these two files. Independent full rebuild under the reviewer's private module prefix follows.
- O2 (Thm3_9 vacuity disclosure is over-cautious): `EnvironmentStage` carries `state_nonempty` and
  `action_nonempty` (`Formalization/MDP/EnvironmentDefinitions.lean:10–11`), and `0 < ε ≤ H` forces `H ≥ 1`,
  so `E 0` exists and S, A ≥ 1 always. The "S = 0 or A = 0 vacuous at N = 0" case is unreachable.

## Independent rebuild (done)

Snapshot copied to the reviewer's private probe folder with only the builder's working module prefix → the reviewer's private prefix
in imports (library and Stmt shas unchanged; Prf shas change only by that rename). Built one at a time with
`bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean <file>` (log in the reviewer's
private probe folder): all 13 modules exit 0, empty output (no warnings, no sorry).
O1 therefore does not affect the verdict: the snapshot text itself compiles.

Axiom re-probe (`ProbeAxioms.lean` in the reviewer's private probe folder, exit 0): all nine `_holds` depend on exactly
[propext, Classical.choice, Quot.sound].

Thm 3.9 probes (`ProbeThm39.lean` in the reviewer's private probe folder, exit 0, same three axioms):
- P1 `thm39_implies_positiveN`: `Thm3_9` implies the verbatim body of `Thm3_9_positiveN`
  (`Formalization/Statements/Ch3.lean:429–454`), with the same `c₀`.
- P2 `thm39_N0_forces_delta_ge_one`: for any `c₀ > 0`, the hypotheses of `Thm3_9` at `N = 0` force `1 ≤ δ`
  (uses `EnvironmentStage.state_nonempty/action_nonempty` and `H ≥ 1`). So the `∀ hN : 0 < N` event (= univ at
  N = 0) is only ever used where `1 − δ ≤ 0`; there is no vacuous instance with nontrivial conclusion. O2 confirmed.

## Source-first reconstruction and verdicts

Sources read before the Lean: MB:255–282, 2524–2585; P:315–360, 490–533; MF:878–900, 940–1000, 3310–3330,
3400–3460; ON:470–507, 788–803. Remark numbering re-derived: MF remarks at 226, 914, 2088, 3451, 3455 → 3455 is
Remark 4.5 (consistent with COVERAGE Remark 4.3 = 2088); ON remarks: bandits.tex:279 (input at ON:202), ON:425,
486, 660, 790 → 790 is Remark 5.5.

### C4 `Thm3_9` (printed, MB:2551–2570): ACCEPT WITH DISCLOSURES (blocking text fix R1)
- Quantifiers: `∃ c₀ > 0, ∀ State Action H E N δ ε, 0<δ → 0<ε → ε≤H → threshold → 1−δ ≤ P{∀ hN, ∀ f, f empirically
  optimal at every (h,s) → V and Q gaps ≤ ε}`. Matches the printed theorem ("for any δ > 0", 0 < ε ≤ H, universal c₀,
  N-free threshold). δ > 0 only, as printed; δ ≥ 1 is trivially true and not excluded, which is faithful.
- Body is token-identical to `Thm3_9_positiveN` except `hN` moved inside the event (diffed).
- `∀ hN : 0 < N` honest, not a vacuity trick: P1 shows `Thm3_9 ⇒ Thm3_9_positiveN` (same c₀); P2 shows that at
  N = 0 the hypotheses force δ ≥ 1, so the univ-event at N = 0 only ever meets the trivial region 1 − δ ≤ 0.
  The printed theorem at N = 0 is a well-defined instance (threshold has no N) whose premise fails for δ < 1; the
  Lean entry reproduces exactly that. Hence the move from "restricted" to "printed" is justified.
- Wrapper (Ch3Prf) follows CHECK C4-a: N = 0 via `samplingLaw_probability`/`probReal_univ`, no threshold argument;
  N > 0 via library `exists_universal_anyEmpiricalOptimalPolicy_sample_constant` (X1-compliant, not a `_holds`).
- **R1 (required before landing).** The S = 0 / A = 0 vacuity disclosure is wrong in the opposite direction:
  `EnvironmentStage` has `state_nonempty`/`action_nonempty` (`MDP/EnvironmentDefinitions.lean:10–11`) and
  0 < ε ≤ H forces H ≥ 1, so S, A ≥ 1 always and there is no vacuous case. Replace, in the `Thm3_9` docstring, the
  drafted COVERAGE row 87 text, the ledger `statement_scope`, and the SOURCE-ISSUES bullet, the sentences
  "With S = 0 or A = 0 … vacuous at N = 0" by: "S, A ≥ 1 and H ≥ 1 are forced (nonempty stage types, 0 < ε ≤ H), so
  at N = 0 the printed threshold implies δ ≥ HSA ≥ 1 and the claim is trivial there; the entry is never vacuous."
  Likewise the proposed patch to the `Thm3_9_positiveN` docstring ("append when S, A ≥ 1 …") should instead say
  S, A ≥ 1 is automatic. Suggested ledger `statement_scope`: "printed; for every deterministic policy optimal for
  the empirical MDP at every stage and state (no tie rule fixed; prelim.tex:738–739); the empirical model is typed
  by a `0 < N` witness inside the event, which at N = 0 is reached only when δ ≥ 1".
- Ledger repoint draft (lean_statement → `Thm3_9`, proof → `Thm3_9_holds`, keep positiveN/causal entries): agree,
  after R1. Cite this file (`critic-trivial-c.md`) as evidence.

### C1 `Lemma2_1_iterationCount` (P:357–360): ACCEPT
Binders identical to `Lemma2_1`; ε > 0 outside the conjunction; "no more than X iterations" read as "every k ≥ X
works" (k = ⌈X⌉ suffices; standard ceiling reading, stronger than an existence claim). Q₀ = Q⋆ junk `log 0 = 0`
gives the correct conclusion and is disclosed. Library route `value_iteration_count`/`…PolicyIteration_count`.

### C2 `Eq_Qpi_Vpi_matrix_notation_inf` (P:496–531): ACCEPT
All five displays present ((a) vector form with P : (S·A)×S, (b), (c), intermediate Q = r + γP^πQ, (d)). P_π and
P^π token-identical to `Lemma2_3` (Ch2.lean:92–95). V^π = Π^πQ^π per eq:Vpi-a-function-of-Qpi-inf. Inverses are
genuine (IsUnit from the resolvent), so no junk `⁻¹`. Every stationary randomized policy.

### C3 `Eq_Vhatpi_Vpi_difference_decoupled_Hoeffding` (MB:270–276): ACCEPT
Universal C₀ before all of S, A, N, M (hence γ), π, δ. Strict `1 − δ <` = "with probability exceeding 1 − δ",
as printed (stronger than plan's ≤; fine). N ≥ 1 as a binder is the faithful domain (display divides by N).
S = 0 impossible (`DiscountedMDP.state_nonempty`, used in proof). Witness 2√720 verified
(`PolicyEvaluationUniversalConstant.lean:18`). Proof route differs from the printed Hoeffding route; drafted COVERAGE
row discloses this. δ ∈ (0,1) matches the regime where log(S/δ) ≥ 0.

### C5 `Thm4_7_iterationLowerBound` (MF:992–1000): ACCEPT
Quantifier order identical to `Thm4_7` (M after γ, T, η; ε after M — M is ε-free, fine). Ω̃ made explicit as
T log²T ≥ c_lb/((1−γ)⁴ε²), a legitimate Ω̃ reading. Regime witness max(c₃,1) (C5-a) forces T ≥ 16, log T > 0;
raising c₃ only shrinks the regime (sufficiently large c₃, as printed). Uses `qLb_thm47` (X1).

### C6 `Thm4_6_constantRate` (MF:945–953): ACCEPT
∀ c₁ ≥ c₂ > 0 (stronger than "small enough"), 0 ≤ γ < 1 (stronger than [1/2,1)), ε ≤ 1/(1−γ) dropped (stronger),
T ≥ 2, δ ∈ (0,1), S, A ≥ 1. "T ≍" used in ≥ direction only, which is the direction an upper bound on η needs.
Algebra re-derived: η ≤ log³T/(c₁(1−γ)T) ≤ (1−γ)³ε²/(c₁c₃ log T log(SAT/δ)). Unused `0 ≤ γ` harmless.

### C7 `Remark4_5` (MF:3455–3457): ACCEPT WITH DISCLOSURES (no suffix needed)
- (ii) is the printed single-action claim: the recursion is eqn:Qhat-schumann with one action
  (Q̂_0 = Q⋆(1,a) = 1/(1−γp), V̂ = Q̂, P_{k+1}(1|1,a) = `qLbStay … 1 (k+1) a`, an indicator, defined at
  `QLearningLowerBoundDefinitions.lean:58`), and ξ is eqn:defn-xi-t with that V̂. The only representation choice
  is the probability space: expectation is under the two-action hard instance's law, but the integrand depends only
  on the action-a state-1 draws, whose law (`qLbRowSpec`: P(1|1,a) = p for every a, independent over k) is the
  single-action law. This is a faithful encoding (same as reading "single action" inside Lemma 4.15's instance), so
  CHECK C7-b route (i) is satisfied and `_restricted` is not required. The drafted COVERAGE row discloses the
  representation; keep that sentence (F2 below). ξ_max = ξ(a) for one action is left implicit (trivial).
- (i) extra generality (any W adapted to state-1 draws up to k−1, matching `qLbAgree1`); not vacuous.
- (iii) positivity on t ≥ τ̂ in Lemma 4.15's regime, binder structure identical to `Lemma4_15`; c₃' = max(c₃,1)
  (C7-a). Reading on t ≥ τ̂ is necessary (ξ = 0 at t = 0) and disclosed.

### C8 `Remark5_5_corrected` (ON:790–802): ACCEPT
Covers every stage h (source h = 1), every history, every L, c₁, c₂. Unfolds to `actionMaximum (onlineCappedStageQ …)`
and the planner's `Classical.choose_spec` (`CappedGreedyPlannerDefinitions.lean`). The planner is the one deployed by
`Thm5_2_corrected`. Suffix: conservative but appropriate since the tables are the C8 zero-count-completed ones
(F7: no-suffix would also be defensible; not required).

### C9 `Eq_regret_asymptotic_ucbvi_corrected` (ON:491–506): ACCEPT
Diff against `Thm5_2_corrected`: only (+) premise `S³AH³ ≤ K` placed before `∃ c₁ c₂` in `Fintype.card` terms
(CHECK placement) and bound `20(√(SAH³K)+S²AH³)(1+I)` → `40√(SAH³K)(1+I)`. "≳" with constant 1 is the weakest
premise among constants ≥ 1, so the claim implies the printed one for any larger burn-in constant. C8 inherited.
Uses library `onlineUCBVI_actual_regret_burnIn` route (X1).

## Cross-cutting checks
- X1: the five new library files import only library modules (direct imports; transitive closure reaches
  `Statements.Ch3Definitions` only through already-frozen G2 edges, e.g. `Generative/ModelBasedPolicyEvaluation`).
  No `*_holds` cited from library code.
- Statement files: import lists identical to live `Ch2/3/4/5.lean` (no new Statements imports, G2 untouched).
  Proof files: every non-WIP import already in live `ChNProofs.lean`, except Ch3Prf's
  `Generative.FiniteHorizonGenerativeSampling` (transitively present via `FiniteHorizonAnyTieSample`; lead may drop or
  keep the explicit line).
- Forbidden tokens: none (`sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`,
  `opaque`, `set_option`) in any snapshot file.
- Junk values: reviewed `log 0` (C1 disclosed; C4 unreachable per P2), `x/0` (C5/C7 guarded by T ≥ 16; C6 by T ≥ 2;
  C3 by N ≥ 1), matrix `⁻¹` (C2 genuine), `Nonempty` instance proof irrelevance (C8). No junk-driven truth found.

## R-items (required)
- R1: correct the S = 0 / A = 0 vacuity wording for Thm 3.9 (docstring of `Thm3_9`, COVERAGE row 87 draft, ledger
  `statement_scope`, SOURCE-ISSUES bullet, and the proposed `Thm3_9_positiveN` docstring patch). See C4 above.

## F-items (non-blocking)
- F1: builder oleans for `Ch2Stmt`/`Ch3Stmt` predate their final source edits (O1); builder `axiom-probe.out` thus
  certified slightly older text. Superseded by this critic's clean rebuild of the exact snapshot. Lead's integration
  build must recompile anyway.
- F2: keep the C7 COVERAGE sentence on the representation of the single-action experiment (law of the action-a
  state-1 draws); no SOURCE-ISSUES bullet needed.
- F3: C1 COVERAGE row could say "k = ⌈log(‖Q₀−Q⋆‖/ε)/(1−γ)⌉ iterations suffice" to make the rounding explicit.
- F4: C8 `_corrected` suffix is conservative (F7); acceptable as is.

## Evidence / hashes
Snapshot sha256 (verified, = the builder's snapshot hash list, live identical):
Ch2Prf bff684c1…, Ch2Stmt f37bb618…, Ch3Prf 0834da43…, Ch3Stmt 95674c2c…, Ch4Prf bd5536cf…, Ch4Stmt 9161f809…,
Ch5Prf 8d99a9b2…, Ch5Stmt 9342afc2…, GreedyValueIdentity e30cbe60…, IterationCount 868344dd…, MatrixBellman db0bba88…,
PolicyEvaluationCrude 85f4c55b…, QLearningRateFacts 912f6050….
Commands: `bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean <probe folder>/<X>.lean`
for the 13 modules (all exit 0), then `bash scripts/lean-local.sh <probe>` for `ProbeThm39.lean`, `ProbeAxioms.lean`
(exit 0). Log: kept in the reviewer's private probe folder. No lake, no lean-lsp, nothing under
`Formalization/` touched.
62c5d692d5921ee3132f91906cd5c41d72cdbcdeba47e99cf53ab4ae82624e1f  ProbeAxioms.lean
d9d494b9fd4f4584a3dfdc254b4686058200be3e1dc67b8fb7baf19aeda0f481  ProbeThm39.lean
