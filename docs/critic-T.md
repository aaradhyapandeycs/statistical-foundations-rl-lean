# Critic review: completion batch T (tooling and docs)

Public copy, scrubbed (local paths removed). All required fixes F1–F7 and recommendations R1–R5 were applied
by the builder after this review; R6 is recorded as a follow-up. Line numbers of `docs/COVERAGE.md` and of the
statement files refer to the reviewed working tree and may have moved.

Date 2026-11-09. Read-only critic (no Lean, no git change; only this file written). Branch
`recovery-batch-fhlb-thm39-sb2a-20261108`, dirty tree. Source: `source/upstream/tex/chapters/` (offlineRL
sha256 prefix `67cf0d1ce6a3`, matches C50). Diffs taken against the builder's saved pre-change copies.

## Verdict: ACCEPT WITH FIXES

The closing statuses are implemented fail-closed and honestly: no implied / explanatory / cited-out-of-scope
row can make a node or a numbered result count as proved (named counts 45/30/15 = 90/90 unchanged, all
closing counts 0 for named nodes; prose proved status needs a non-closing reviewed row). The wrapper-body fix
removes only bleed. Most rows are accurate. Required fixes: one factual error in C50 (and its COVERAGE row),
two "Implied by" rows that claim a minimax comparison the cited entries do not give, a wrong count in
PROGRESS, two explanatory line ranges that swallow proved/labelled material, and the "Ready" heading.

## Commands run

- `python3 scripts/gen_nodes.py --check` -> `ok: docs/graph/nodes.json and docs/NEXT.md are current` (rc 0).
- `python3 -m unittest discover -s scripts/tests` -> `Ran 119 tests ... OK` (the "stale generated files"
  line in the log is a test fixture's expected output, not the repo).
- `python3 scripts/static_gates.py` -> G1, G2, G3 (174 entries, 174 `_holds`), G4 ok; **G6 FAIL, 34 errors,
  all in the untracked `Formalization/Analysis/ConvexSmoothIndicator.lean`** (and its shell sibling;
  namespace outside `StatisticalRL`). That file belongs to the all-convex 7.11 M2 builder, not batch T. Not a
  T defect, but G6 must be green before any PR that includes it (or the file must stay out of the PR).
- No site rebuild (builder reports 174/174 placed, fidelity OK; not re-run here).

## 1. Diffs vs orig (all changed files read)

README (one sentence), PROGRESS (triage section, ownership row, out-of-scope sentence), SOURCE-ISSUES (C50
only), COVERAGE (67 new rows; edits to rows 64, 71, 72, 91, 99, 114, 143), gen_nodes.py, test_gen_nodes.py
(+7 test methods), site/reader graph/lean/render. Edits to rows 64/71/72/91 add **Supporting ...** leads;
row 72 now says Theorem 7.5 is proved in corrected form, which matches the ledger. Row 143 (Remark 6.3) now
says sentences 1–3; the node is `partial`, matching PROGRESS. No other content was changed.

## 2. Explanatory rows (sampled 22 of 29 against the TeX)

Checked: prelim 1231–1235 (Rem 2.1), prelim 76, prelim 225–228, MB 1187–1189 (Rem 3.1), MB 1412–1419
(Rem 3.2), MB 340–376, MB 975–1122, MB 1212–1218, MF 14–54, MF 1003–1013, ON 599–672, ON 615, ON 425–429
(Rem 5.2), ON 660–662 (Rem 5.4), ON 963–965 (Rem 5.7), ON 2043–2047 (Rem 5.11), OFF 505–515, OFF 1192–1199
(Rem 6.6), OFF 1539–1541 (Rem 6.7), OFF 1695–1697 (Rem 6.8; Lean lines 59/72 and FiniteLCBQ line 77
verified), OFF 1894–1896, OFF 1789–1793, INF 144, marl 247, FED 157–160, RLHF 74, intro/cousins/conclusion.

None hides a theorem-level claim. Problems are in wording and ranges:

- **E1 (range, required).** "Asymptotic conclusion ..., model-based chapter lines 340–376" overlaps the
  proved displays `eq:I-gamma-P-Var-bound` (335–342) and `eq:lemma-VarP-V-bound` (348–352), row 107. The
  heuristic starts at 354.
- **E2 (range, required).** "Heuristic regret decomposition, ..., online-RL lines 599–672" contains Lemma 5.3
  (`lem:sum-inv-Nhk-ucbvi`, 638–646), Lemma 5.4 (648–658) and Remark 5.4 (660–662), which have their own
  rows. Exclude them.
- **E3 (wording, required).** "First-attempt policy-learning analysis, MB 975–1122" contains exact
  statements (e.g. the identities `eq:Vhat-V-pihatstar-identity-246`/`-2468`, the concentration display
  `eq:Phat-pistarhat-bernstein`), not only heuristics. "No mathematical claim" is acceptable for the passage
  as a heuristic argument only if the row says its intermediate displays are proof steps of that heuristic and
  are not separately formalized.
- **E4 (wording, required).** Prelim line 76: the row says the sentence's "precise content" is
  `Eq_optimal_Vstar_Qstar_defn` (deterministic stationary optimal among stationary policies). The sentence is
  about restricting to time-invariant policies, i.e. against time-varying / history-dependent ones, which is
  not what that entry proves. Line 76 (not 66, as the check wrote) is the correct locator; the deviation is
  accepted.

## 3. Implied rows (all 21 checked)

Entries opened: `Lemma4_15` (conjunct `∃ τ, ρ^{T+1−τ} ≤ 6/7 ∧ maximal`, Ch4.lean:352), `Lemma5_7_K2_corrected`
(W₃ conjunct), `Lemma5_9_K2_corrected` (second event, simplified clauses), `Lemma5_14_corrected`,
`Eq_online_RBMLE_restricted` clause (a), `Thm6_8_corrected`, `Thm3_9`. Suffixes are carried in nodes.json
(`implied_variant`: corrected/restricted/printed as expected) and every one of the 16 Õ rows says "The Õ form
is not formalized as a separate Prop". The generator fails if an `Implied by` entry's own node is not proved.

Two rows overclaim:

- **I1 (required). "TD sample-size read-off, model-free chapter lines 240–251".** TeX 248–249: TD "attains
  minimax-optimal sample complexity" by comparison with Theorem 3.7 at A = 1. The row heads
  `Implied by Thm4_1 and Thm3_7_corrected` and then says the comparison is not covered (`Thm3_7_corrected`
  needs A ≥ 2, C1). A claim the row itself says is not covered cannot be under an "Implied by" headline that
  names the entry that fails to cover it. Same pattern the plan check used for Remark 4.5 (C2: the A = 1
  side keeps the node partial).
- **I2 (required). "Minimax optimality of the model-based approach, model-based chapter lines 1468–1474".**
  TeX 1471: optimality "for both policy evaluation and policy learning, across the entire range of ε". The
  policy-evaluation half needs an A = 1 lower bound, which `Thm3_7_corrected` does not give (row says so),
  and the corrected regime (S ≥ 2, A ≥ 2, SA ≥ 16, γ ≥ 2/3) does not cover the whole printed range.
- **I3 (observation, pre-existing, not a T defect).** `label:eq:sample-size-finite-horizon-generative` is
  `printed / proved` (from row 120, `Thm3_9_minimaxLowerBound`, which proves the minimax sentence at 2585),
  while the new row 216 says the Õ(SAH⁴/ε²) display itself is only implied. NEXT shows "also implied
  (COVERAGE.md:216)". The node title is the display, so its "printed proved" status really rests on the
  adjacent prose claim. Record as a follow-up for the generator/ledger (e.g. attach row 120 to a prose node
  for line 2585), not blocking T.
- Accepted with note: `eq:QT-gamma-5-Q-learning-generative` (the explicit first line is a proof step of a
  first-attempt argument; disclosed). `eq:RLHF-policy` implied by clause (a) only for minimizers that exist
  (C44; disclosed).

## 4. Cited-out-of-scope rows (all 16 checked; all carry `user decision 2026-11-09`)

Counts: 16 rows = 5 remark nodes (5.1, 5.3, 6.1, 6.9, 7.3) + Remark 6.3 sentence 4 (attached to the
`partial` Remark 6.3 node) + 10 rows without node. All are cited from the literature and none states a
precise result about the book's own objects that the book itself develops.

Rulings on the builder's deviations:
- **A17, RLHF 218–234 (adaptive calibration) as cited-out-of-scope instead of explanatory: ACCEPT.** Line
  233 asserts a regret rate T^{(β+1)/(β+2)} "up to polynomial dependency" for a variant credited to
  li2025towards; that is a cited claim, so out-of-scope is the more conservative status.
- **MF 3956–3995 (Notes) as cited-out-of-scope: ACCEPT.** It contains cited minimax claims (wainwright2019variance;
  "no existing model-free algorithm ... ε ≫ 1"), which are claims about the literature, not explanatory text.
- **OFF 3121 (finite-horizon VI-LCB minimax optimality, li2024settling): ACCEPT.** The finite-horizon lower
  bound and its class are not stated in the book.
- **jin2018q (ON 1923–1929): ACCEPT.** A Bernstein UCB-Q is not defined in the book.
- **Prelim line 76 (explanatory) instead of 66: ACCEPT** (the sentence is at 76), with E4's wording fix.
- **Q-FTRL row (marl 426–470), recommended wording fix R1.** Its range contains Theorem 7.7 (441–467), which
  is counted as `restricted`. The row is correct only as "the residual of Theorem 7.7 that
  `Thm7_7_restricted` does not cover". Not attached to the named node (verified), so no count is affected.

## 5. C50

Lines verified: theorem 1754–1772, claim 1778–1789, display 1781–1783, VR citations 1794–1799, sentence has
no citation of its own, Theorem 6.8 header "[Yan et al. (2022)]". `Thm6_8_corrected` (Ch6.lean:574–618)
requires `c₂ S C⋆ log²(SAT/((1−γ)δ)) / ((1−γ)⁵ ε²) ≤ T`: (1−γ)⁻⁵, so item 4 ("does not imply (1−γ)⁻⁴") is
accurate.

**C1 (required): item 1 is false as written.** "The Bernstein-style penalty is not defined anywhere in the
book" — the book defines a Bernstein-style penalty for VI-LCB (`def:bonus-Bernstein-infinite`,
offlineRL.tex:808–824, motivated at 789–802) and a Bernstein bonus for UCBVI/MVP
(`eq:bh-defn-Bernstein-ucbvi`, onlineRL.tex). What is undefined is a Bernstein-style penalty **for LCB-Q**.
The same error is in the COVERAGE row ("the book does not define the Bernstein-style penalty").

## 6. gen_nodes

- New statuses cannot count as proved: prose `proved` requires `statement_entries` **and** a non-closing
  reviewed row; named `proved` comes only from ledger records; closing statuses only apply when
  `not reviewed_rows`; test `test_closing_statuses_never_count_as_proved` covers it. Summary: named closing
  counts all 0; `closing_not_proved` is separate.
- Out-of-scope rows without the dated anchor make the generator exit (`closing_info`); implied rows must name
  entries with exactly one `_holds` and a proved own node.
- **Wrapper-body fix: correct.** Compared library_exports old vs new for all nodes: 31 removals, all bleed
  (namespace tokens `StatisticalRL.Statements`, `StatisticalRL.Ch7Rest.Rlhf`, `RobustRL.Ch7`/`DRVI` from
  `open` lines; names from the next wrapper's docstring). Spot-checked 5: `lemma:dual-form` (qChiBall,
  qChiSquared, valueMin_le … came from private helpers after `Lemma7_1_tv_holds`, which ends at line 64);
  `eq:convex.Cdelta` (`eq_defn_hat_Lambda_corrected` is from the next wrapper's docstring at 436);
  `eqn:classic-clt` (`exists_coverage_oracle_bounds` belongs to the next wrapper); `remark:tv-upper`
  (`chi_oracle_planner_guarantee` is Remark7_2's, line 220); `eq:calibrated_value`
  (`thm7_6_restricted`, line 315). Each node keeps its real export. Latent: a column-0 `--` or `#` line
  inside a proof would end a body early (only loses exports of unrecorded entries).
- **Remark attachment: no misattachment now.** Entry->node changes: Remark6_3 (display -> remark),
  Remark5_13_corrected (display -> remark), three Ch2 joint displays (correct per rows 93–95), and
  `Eq_convex_distance_le_TV` additionally attached to `label:eq:TV` (row 32 lists `eq:TV` only as context
  in parentheses; harmless to counts since `eq:TV` was already proved, but wrong — R2). The "largest inner
  result inside the first range" rule could misattach an entry whose first range is a long proof span
  containing a remark or lemma (R3).
- Closing rows attach to a node only by a label or a leading numbered reference. Nothing prevents a future
  closing row from closing a **numbered** result and so removing it from NEXT's open list (R4).

## 7. Site wording

grep of `site/reader/*.py`: every new string says "not separately proved", "nothing proved", "not proved" or
"never counted as proved"; none calls these statuses proved. Accepted. NEXT heading at line 17 is now
inaccurate (F6).

## Required fixes (exact text)

**F1 (C50 item 1, SOURCE-ISSUES.md).** Replace item 1 with:

> 1. No Bernstein-style penalty is defined for LCB-Q. The book defines Bernstein-style penalties only for the
>    model-based VI-LCB (`def:bonus-Bernstein-infinite`, `:808–824`) and the UCBVI/MVP bonus
>    (`eq:bh-defn-Bernstein-ucbvi`, `chapters/onlineRL.tex`); both use empirical variances of an estimated
>    transition model, which LCB-Q does not maintain. For LCB-Q only the Hoeffding-style penalty
>    `eq:stepsize-penalty-offlineQ` (`:1666–1687`) is specified; the constants and variance estimate of a
>    Bernstein variant, and any change to its learning rate, are not given.

**F2 (COVERAGE row "Bernstein-penalty LCB-Q sample size").** Replace "and the book does not define the
Bernstein-style penalty, the learning rate or the threshold on ε" with "and the book defines no
Bernstein-style penalty for LCB-Q (only for VI-LCB and UCBVI/MVP), nor its learning rate or the threshold on ε".

**F3 (COVERAGE row "TD sample-size read-off, model-free chapter lines 240–251").** Replace the cell after
`none |` with:

> **Implied by `Thm4_1`.** Õ(S/((1−γ)³ε²)) samples (S per iteration times Theorem 4.1's iteration count,
> log factors dropped). The Õ form is not formalized as a separate Prop (decision F1, 2026-11-09). **Not
> implied, open:** the minimax-optimality claim (lines 248–249), which compares with Theorem 3.7 at A = 1;
> `Thm3_7_corrected` needs A ≥ 2 ([C1](SOURCE-ISSUES.md#C1)), so no A = 1 lower bound is formalized.

**F4 (COVERAGE row "Minimax optimality of the model-based approach, model-based chapter lines 1468–1474").**
Replace the cell after `none |` with:

> **Implied by `Thm3_2_positiveN` and `Thm3_7_corrected` (policy learning, in the corrected lower-bound regime
> only).** Comparison of Theorem 3.2's upper bound with the corrected Theorem 3.7 lower bound "up to
> logarithmic factors", in that entry's regime S ≥ 2, A ≥ 2, SA ≥ 16, γ ≥ 2/3 ([C1](SOURCE-ISSUES.md#C1),
> [C2](SOURCE-ISSUES.md#C2)). The Õ comparison is not formalized as a separate Prop (decision F1, 2026-11-09).
> **Not implied, open:** the policy-evaluation half (Theorem 3.1 against a lower bound at A = 1, which no
> entry gives) and optimality outside the corrected regime ("across the entire range").

**F5 (PROGRESS.md triage paragraph).** Replace "(5 remarks and 10 unlabelled passages, including sentence 4
of Remark 6.3, so Remark 6.3 stays partial)" with "(16 rows: 5 remarks, sentence 4 of Remark 6.3, so Remark
6.3 stays partial, and 10 unlabelled passages)". In the same paragraph replace "the federated read-off (C41),
and the all-convex Theorem 7.11 bound" with "the federated read-off (C41), the A = 1 minimax-optimality
comparisons for TD learning and model-based policy evaluation (C1), and the all-convex Theorem 7.11 bound".

**F6 (gen_nodes.py, NEXT heading).** Change the "Ready" heading text from "Ready: open nodes whose candidate
uses are all proved" to "Ready: open nodes whose candidate uses are all proved, implied or explanatory", then
regenerate.

**F7 (COVERAGE explanatory ranges/wording).**
- Row "Asymptotic conclusion of the second policy-evaluation attempt, model-based chapter lines 340–376":
  change "lines 340–376" to "lines 354–376" in the item.
- Row "Heuristic regret decomposition, `eq:ovr-est-ub2` and `eq:ovr-est-ub1`, online-RL lines 599–672":
  change "lines 599–672" to "lines 599–637 and 663–672 (Lemmas 5.3, 5.4 and Remark 5.4 at 638–662 have their
  own rows)".
- Row "First-attempt policy-learning analysis, model-based chapter lines 975–1122": after "motivating the
  sharp analysis;" insert "its intermediate displays (for example `eq:Vhat-V-pihatstar-identity-246` and
  `eq:Phat-pistarhat-bernstein`) are steps of that heuristic argument and are not separately formalized;".
- Row "Time-invariant policies suffice, preliminaries line 76": replace the cell text after the bold lead
  with "\"It is typically sufficient to restrict attention to time-invariant policies\" is a hedged scoping
  remark with no precise statement. The book's policy class is stationary throughout (line 66); optimality of
  stationary policies against time-varying or history-dependent ones is not formalized (the related proved
  fact, a deterministic stationary policy optimal among stationary policies, is `Eq_optimal_Vstar_Qstar_defn`).
  Category reviewed in the completion plan check (2026-11-09; locator corrected from line 66). No statement
  entry."

After F1–F7: regenerate (`python3 scripts/gen_nodes.py`), rerun `--check`, unittest and static_gates (G6
expected to fail only on the untracked all-convex files until those are fixed or excluded).

## Recommended (non-blocking)

- **R1 (Q-FTRL row).** Item: "Q-FTRL algorithm (omitted at line 432) and the residual of Theorem 7.7 that
  `Thm7_7_restricted` does not cover, multi-agent chapter lines 423–432 and 441–467"; keep the rest.
- **R2 (joint rule).** In `row_confirms_joint`, test only the part of `row["item"]` before the first "(" so
  a context label (row 32's `eq:TV`) is not attached; regenerate and confirm `Eq_convex_distance_le_TV`
  attaches only to `eqn:convex-distance`.
- **R3 (inner rule).** Restrict the "inner result" rule to remarks (PROSE_KINDS remark) or to the case
  where the entry's cited labels all lie inside that result; add a test with a proof-span first range
  containing a remark.
- **R4 (guard).** In the COVERAGE loop, `raise SystemExit` when a closing row targets a node of
  `NAMED_KINDS` (a numbered theorem/lemma must never be closed as implied/explanatory/out of scope).
- **R5 (decision anchor).** Add `<a id="user-decisions-2026-11-09"></a>` before the PROGRESS triage heading
  and make each "user decision 2026-11-09" in COVERAGE link to `PROGRESS.md#user-decisions-2026-11-09`
  (the check's F-T-4 asked for an anchor quoting the user's decision; PROGRESS paraphrases it).
- **R6 (I3 follow-up).** Fix the display-vs-prose attachment of row 120 so the Õ display node is not
  `printed proved` on the strength of the adjacent minimax sentence.

## Publishing the completion plan check

Recommended and done: a scrubbed public copy is [critic-completion-plan-check.md](critic-completion-plan-check.md)
(worker briefs and private paths removed, a private-memory sentence replaced by a dated supersession note, D11
marked as resolved into the open finding C50, and the P:66 locator corrected to line 76).
