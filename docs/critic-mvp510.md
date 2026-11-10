# Critic report: Theorem 5.10 under the literal MVP trigger (C48) (2026-11-10)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of `Formalization/Online/Regret/MVP/Thm510LiteralRefutation.lean` (exports `not_Thm5_10_literalTrigger_printed`, `thm510Literal_regret_eq`). Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT-WITH-FIXES; all fixes applied. The optional per-selector export was added as `not_Thm5_10_literalTrigger_printed_rule`: for every fixed deterministic tie rule (a selector for each finite instance; no argmax premise is needed), `Thm5_10_literalTrigger_printed_rule rule` is false. The C48 entry in `SOURCE-ISSUES.md` uses the status wording proposed below, says the tie is permanent and that every deterministic tie rule fails after relabelling, and no longer says "paper calculation, not Lean-checked" (also in the C13 pointer). The `printed_refuted` ledger entry for `thm-mvp-regret` uses the valid kind `counterexample` (the report's "printed_refuted" is the ledger field name), lists both Lean refutations, and notes that only deterministic tie rules are covered and that c₁, c₂ are universal. The module is imported from `Formalization.lean`. This is a library refutation, not a statement-index entry.

Verdict: ACCEPT-WITH-FIXES (fixes are disclosure/wording; one optional Lean strengthening).

## Evidence
- `bash scripts/lean-local.sh Formalization/Online/Regret/MVP/Thm510LiteralRefutation.lean`: exit 0, no output (3.9 s; olean 11:44:08 newer than source 11:44:05).
- `#print axioms` (scratch `<local probe>`): not_Thm5_10_literalTrigger_printed and thm510Literal_regret_eq -> [propext, Classical.choice, Quot.sound]. No sorry/admit/axiom in file.

## (1) Fidelity of Thm5_10_literalTrigger_printed
- Printed theorem (onlineRL.tex:1339-1352) is a high-probability statement ("With probability at least 1-delta"); Prop is `1 - δ ≤ P(regret ≤ bound)`. Matches; not an expectation.
- Õ: ∃ C (any real), p : ℕ, factor (1+log(SAHK/δ))^p, chosen before instance (intro.tex:192 universal constant). Generous.
- c1, c2 > 0 existential before instance ("universal constants", :413; "suitably chosen", :1350). Correct order. NOTE: refutation genuinely needs c2 independent of K (if c2 could shrink with K, c2 log(1/δ') < 1 avoids saturation). This is the printed order, so fine; disclose.
- Bonus :407-417, clip min{.,H} :1298-1300, V_{H+1}=0, Q=H before first trigger :1262, trigger as printed :1280 (Nat.log 2 K; witness only uses 1 ∈ set, so any reading of 2^{log2 K} >= 1 works), δ' :416, regret eq:defn-regret with actual policies and initial states. Faithful.
- Tie rule: Prop requires the bound for every deterministic argmax selector depending on (h,s,Q-row). This is a stronger demand than "some tie rule", but see (3).

## (2) Genuineness
Not a junk value. Under the literal trigger every visit of a row stores a batch of size 1, so bonus c2·H·log(1/δ')/1 >= H for large K: every visited action's clipped Q equals H forever, and an unvisited action's Q = min{r + b0, H} <= H for ANY completion b0 (b0 >= 0 gives a tie, b0 < 0 or b0 = +inf also keeps bad an argmax). P̂ = 1/S init irrelevant (V_{H+1}=0). So the C8 completion is irrelevant; the tie is caused by the printed clip at H together with the never-decaying bonus, which is structural (for any S,A,H all visited Q-values saturate). Without the clip there would be no tie (good would win) — the counterexample uses the printed clip, not an artefact. δ' polynomial in 1/K or even δ'=δ (choose δ small) also works.

## (3) Every tie selector
Correct: Q-row is constantly 1 in every episode, so sel always returns sel 0 () (fun _ => 1); environment labels that action reward 0; regret exactly K surely (thm510Literal_regret_eq). Uniform random tie-breaking gives regret ~K/2 w.h.p. (not machine-checked). History-dependent tie rules are outside the model; all remain pure tie-breaking with no reward signal in Q.
Fix (optional, recommended): export the per-selector form `∀ sel, ¬ (printed Prop for that fixed sel)` so the "any fixed implementation fails" reading is machine-checked, not just the ∀sel Prop.

## Classification
Genuine refutation of the literal-trigger reading; reading-dependent only on C13 (literal vs dyadic trigger). Not boundary.

## Proposed ledger wording
C48: "Status: confirmed false under the literal trigger reading (C13); machine-checked as `not_Thm5_10_literalTrigger_printed` (Thm510LiteralRefutation.lean). Witness S=H=1, A=2, δ=1/2, large K: every visit triggers with batch size 1, bonus c2·H·log(1/δ′) never decays, all clipped scores saturate at H, so the run is pure tie-breaking; for every deterministic argmax tie rule, relabelling its tie choice as the reward-0 action gives regret exactly K surely (`thm510Literal_regret_eq`), contradicting C·polylog·√(SAH³K). Independent of the zero-count completion (C8) and of the reading of log₂K. Relies on c1, c2 being universal (printed). The dyadic reading is the corrected theorem MVP_regret_corrected."
printed_refuted entry: kind = "printed_refuted", reading = "literal trigger set {1,2,…,2^{log₂K}} (C13); Õ as ∃C,p polylog(SAHK/δ); universal c1,c2>0; any b0>=0; every argmax tie rule".
Also replace C48 phrase "(paper calculation, not Lean-checked)" at SOURCE-ISSUES.md:719 and update its witness text ("breaks the initial tie toward the reward-0 action") to say the tie is permanent and the result holds for every tie rule after relabelling.
