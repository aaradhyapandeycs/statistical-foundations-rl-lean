# CRITIC P3a (Chapter 7 robust Bellman and RLHF displays): independent review

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-09): this critic reviewed the pre-integration drafts. They were integrated on 2026-11-09 into `Formalization/Statements/Ch7.lean` and `Ch7Proofs.lean`. F1–F4 and R1 were applied before landing: F1 scope text in both robust docstrings and COVERAGE rows; F2 renamed the prompt-shift entry to `Eq_calibrated_value_shiftInvariant_restricted`; F3 added the scope sentences to the RLHF bullet of [Statement-index scope disclosures](SOURCE-ISSUES.md#statement-index-scope-disclosures); F4 added the pairwise-difference conjunct to `prompt_shift_invariance`, so the `VPODisplays712.lean` hash differs from the one quoted below and the wrapper now only projects; R1 prints the π_r formula in the `Eq_reward_policy_eq_restricted` and `Eq_Jstar_restricted` docstrings. Labels U13–U16, #35 and #36 number the rows of the builder's draft; F-P3a-n refers to the independent completion check. The review text below is otherwise unchanged.

Critic: independent (not the builder). Date 2026-11-09. Brief: the completion plan, batch P3a, as amended by
the independent completion check, findings F-P3a-1..5.

Reviewed (sha256 match the builder's final build-log hashes):
- `Formalization/RobustRL/DRVI/RobustBellmanDisplays.lean` 16182559…6b21
- `Formalization/Ch7Rest/VPODisplays712.lean` 9f2bfcef…e0
- the builder's statement draft 2efec79c…aad and wrapper draft 6c34db1f…a6c,
  its non-vacuity probe, draft coverage rows, status notes and build log.

Source read independently: `robust_RL.tex:19–140, 250–275`, `RLHF.tex:1–130`, `prelim.tex:62–68`.

## Overall verdict: **ACCEPT WITH FIXES**

The mathematics is right, every entry is non-vacuous, the U14 object is the trajectory object, RowAttains is
proved (not assumed), Z is inline, the eq:Jstar hypotheses are the F-P3a-2 ones and all four printed lines
are stated. Fixes are naming (U16 suffix), scope disclosures (U13/U14 general ρ, U15 supp ρ, U16), and one
wrapper conjunct proved outside the library export.

## Compile / axiom evidence (critic-run)

All runs via the project's local Lean wrapper, one Lean process, started only when `pgrep -x lean | wc -l` < 2.
- a statement-only probe: Ch7.lean's 8 imports verbatim + the statement draft body.
  rc=0, 6 s, no messages. → entries compile with exactly the current Ch7 imports; no new G2 edge.
- a critic probe: `import Formalization` + both new modules + statement
  body + wrapper body (collision check against the whole library) + `#print axioms` + `#print` of entries.
  52 s. All 6 `*_holds` and 3 key library exports: `[propext, Classical.choice, Quot.sound]` (9/9).
  The only errors are in the critic's own trailing sanity `example` (line 307, redundant `norm_num` after
  `simp`: "No goals to be solved"); they are not in builder code. The inline-T^σ = `robustBellman` example
  compiled. `#print` confirms `klDiv` in U15/U16 is `StatisticalRL.Ch7Rest.Rlhf.klDiv` and `sigmoid` is
  `Real.sigmoid`.
- grep `sorry|admit|axiom|native_decide` over both library files and both drafts: no hits.
- Oleans of both new modules are newer than their sources; source hashes equal the build log's final hashes.
- Not run: `lake build`, `python3 scripts/check.py`, `Audit.lean` (lead's integration step).

## Per-entry verdicts

### 1. `Eq_bellman_equ_infinite_all` (U13; `robust_RL.tex:102–113`) — ACCEPT WITH FIX F1
- Full, self-contained: inner infimum written as `⨅ q : ball (P⁰_{s,a}) σ, ∑ q·V` (F-P3a-5 satisfied without
  `rowInf`); objects `robustPolicyQ/Value/OptimalValue` are definitions-module objects (Ch7Definitions),
  actual trajectory infima over (s,a)-rectangular admissible kernels, static adversary — same as the accepted
  `Eq_mdp_value_Q`.
- (1) consistency for every stationary randomized π (book's policy class, `prelim.tex:65`); (2) optimality with
  sup objects; (3) any value-maximizing stationary π⋆ has V^{π⋆}=V⋆, Q^{π⋆}=Q⋆. Hypothesis on π⋆ is *weaker*
  than printed (value-max only, not "maximizes V and Q", not deterministic) → statement is stronger. Fine.
- σ: printed `σ > 0` (`:37`); entry `0 < σ`. Matches (σ = 0 is not printed).
- **Uncertainty sets (F1).** The printed display sits in the general framework of `:36–46` ("ρ a distance-like
  metric"); TV and χ² are "two popular instances … the primary focus of this section" (`:52`). The entry covers
  only these two instances. Since "distance-like metric" is not a defined class (the general claim has no
  determinable formal content, e.g. attainment for non-closed balls) and the accepted precedent
  `Eq_mdp_value_Q` uses the same two balls with no suffix, I do **not** require `_restricted`; but the docstring
  says "No source issue. Stronger than printed …" and must also disclose the scope. Required text in F1.
- Also disclose (as `Eq_mdp_value_Q` does) that "π stands for any policy" is read as stationary randomized
  policies; history-dependent policies / dynamic adversary not claimed.

### 2. `Eq_robust_bellman_fixedPoint` (U14; `:114–133`, `:261–262`) — ACCEPT WITH FIX F1
- F-P3a-3 satisfied: `Qs := robustPolicyQ ball M σ πs` for an **arbitrary** stationary πs maximizing robust value
  (trajectory object, not `optQ`/operator fixed point by definition). Bridge `robustPolicyQ_eq_optQ_of_dominates`
  is genuine (mutual domination via `policyFix_le_optFix` and the deterministic `optPolicy`).
- T^σ written out with `V(s)=⨆ b, Q(s,b)` (`:118–127`); (a) fixed point, (b) every fixed point = Qs, (c)
  sup-norm γ-contraction, (d) geometric convergence from any Q₀ (`:132` "arbitrary initialization"), (e) DRVI
  from 0 within γ^t/(1−γ) (`:268` Q̂₀=0). Nominal kernel arbitrary ⇒ covers T̂^σ / Q̂^{⋆,σ} of `:261` by
  instantiating M with the empirical nominal model. Correct.
- RowAttains for both balls: `tvBall_family_rowAttains`, `chiBall_family_rowAttains` (DRVI/Optimality.lean:183,
  187), proved from `σ ≥ 0`. Not a hypothesis. ✓
- Non-vacuity of the πs hypothesis: non-vacuity probe example 1 (from `exists_det_robust_value_Q_optimal_tv/chi`). ✓
- Same scope disclosure as entry 1 (F1).

### 3. `Eq_reward_policy_eq_restricted` (#35; `RLHF.tex:62–66`) — ACCEPT
- Z inline (F-P3a-1) ✓; `gibbsPolicy` is a definitions-module def (VPODefs712:45, transparent closed form) —
  acceptable; `partitionFn` (proof module) not used ✓. β>0 printed `:47` ✓. Suffix `_restricted` for full-support
  π_ref / finite X,Y, consistent with `Eq_DPO_restricted` ✓ (existing scope disclosure covers it; add the name,
  see SOURCE-ISSUES text below).

### 4. `Eq_Jstar_restricted` (#36; `RLHF.tex:115–124`) — ACCEPT
- F-P3a-2 satisfied: hypotheses `ρ ≥ 0`, `IsCondPolicy π_cal`, `IsPositivePolicy π_ref`, `β>0`; no `∑ρ=1`.
- All printed lines stated: first line (`:118–119`, π_r expectation of r − β(log π_r − log π_ref), minus
  E_{ρ,π_cal} r), log Z line (`:120`), (i) (`:121`), (ii) (`:122`), each equated with `optCalValue` =
  sup over conditional policies of the calibrated value (`eq:Jstar_calibrated`, `:99–102`). Z inline ✓.
- Suffix `_restricted` (full-support π_ref, finite X,Y) ✓.

### 5. `Eq_RLHF_policy_closed_form_restricted` (U15; `RLHF.tex:41–59`) — ACCEPT WITH FIX F3
- J(r,π) and π_r written out inline; `klDiv` resolves to `StatisticalRL.Ch7Rest.Rlhf.klDiv`
  (∑ p log(p/q), VPODefs712:53), which is the true KL for full-support π_ref (the hypothesis) ✓.
- Conclusions: π_r conditional policy; maximizes J over all conditional policies; a conditional policy maximizes
  iff it equals π_r on supp ρ. This is the correct characterization; with full-support ρ it yields the printed
  uniqueness verbatim. Off-support non-uniqueness witness machine-checked (non-vacuity probe example 3) ✓.
- `_restricted` is the right suffix (approved in CHECK §2). Needs the new SOURCE-ISSUES scope sentence (F3).

### 6. `Eq_calibrated_value_shiftInvariant` (U16; `RLHF.tex:90–98`) — ACCEPT WITH FIXES F2, F4
- Conjuncts: (a) pairwise differences (`:90`), (b) BT NLL equality for every dataset (`:90`, `eq:MLE`
  `:37–39`), (c) uncalibrated J⋆(r₁)=J⋆(r₂)+E_ρ c (`:90`, F-P3a-4 ✓), (d) calibrated value equality for every
  conditional π (`:98`), (e) calibrated J⋆ equality. All printed claims present; J written out inline ✓.
- **Suffix ruling (F2): rename to `Eq_calibrated_value_shiftInvariant_restricted`.** The entry assumes
  full-support π_ref (`IsPositivePolicy`), which the printed claim at `:90–98` does not need: with the
  extended-real KL (KL = +∞ off π_ref's support) every printed conjunct holds for any π_ref (J⋆ is finite since
  π = π_ref is feasible). The hypothesis is there only because the Lean `klDiv` (Real.log 0 = 0 junk) equals
  the true KL only under full support. That is "the export assumes more" → restriction under AGENTS.md, and it
  is the same reason `Eq_reward_policy_eq_restricted` and `Eq_Jstar_restricted` carry the suffix; for U16 the
  case is even stronger since no `log π_ref` appears in the printed claim. Dropping the hypothesis would not
  help: without it the Lean J is a junk object, not the book's J.
- **Wrapper (F4).** Conjunct (a) is proved by `ring` inside `Eq_calibrated_value_shiftInvariant_holds`, not
  taken from a library export. Trivial, but the wrapper rule is "apply the library theorem". Add (a) as a
  conjunct of `prompt_shift_invariance` (VPODisplays712.lean:307) and have the wrapper only project.

## Required fixes

- **F1 (docstrings of `Eq_bellman_equ_infinite_all` and `Eq_robust_bellman_fixedPoint`).** Replace
  "No source issue." by: "No source issue. Scope: the source states these displays for a general
  `(s,a)`-rectangular set built from a 'distance-like metric' ρ (`:36–46`); the entry covers the two instances
  the section focuses on (`:52`), the TV ball and the χ² ball. Other choices of ρ are not claimed. As in
  `Eq_mdp_value_Q`, 'any policy' is read as the book's stationary randomized policies (`prelim.tex:65`);
  history-dependent policies and dynamic adversaries are not claimed." (For U14 use the same text with
  "this operator and DRVI claim" in place of "these displays".)
- **F2.** Rename `Eq_calibrated_value_shiftInvariant` → `Eq_calibrated_value_shiftInvariant_restricted`
  (entry, `_holds` wrapper, COVERAGE row, named-result-status if listed). Docstring: replace the last
  paragraph by "Restricted (`docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`): full-support `π_ref`
  and finite `X`, `Y`, as in `Eq_DPO_restricted`. The printed claims hold for every `π_ref` with the
  extended-real KL; the hypothesis is needed because the formal `klDiv` equals the KL divergence only when
  `π_ref` has full support. Only (c) uses `π_ref` and `β` in the proof."
- **F3.** Add the SOURCE-ISSUES scope sentences below (lead-only edit).
- **F4.** Move conjunct (a) of U16 into the library export `prompt_shift_invariance`; wrapper only projects.

Recommended (non-blocking):
- R1. `Eq_reward_policy_eq_restricted` and `Eq_Jstar_restricted` use the named `gibbsPolicy` while U15 inlines
  π_r. Both are acceptable (`gibbsPolicy` is a transparent definitions-module def); for reader uniformity the
  docstrings could print the formula `π_r(y|x) = π_ref(y|x) exp(r(x,y)/β)/Z(r,x)` (Eq_Jstar's docstring already
  names it the Gibbs policy).
- R2. U13/U14 docstrings: "the library needs only `σ ≥ 0`" — fine; keep.

## COVERAGE text (approved with these edits to the draft rows)

- Row U13: approved after adding, at the end of the scope cell before "Awaiting": "TV and χ² instances only
  (`:52`); the general distance-like ρ of `:36–46` is not claimed; stationary randomized policies only."
  Replace "Awaiting independent critic." by "Critic: [CRITIC-p3a] accepted with F1." (or the project's usual
  reviewed wording).
- Row U14: same addition.
- Row #35, #36: approved as drafted.
- Row U15: approved; replace "needs a new sentence for the supp ρ point" by nothing (the sentence is added, F3).
- Row U16: change the entry name to `Eq_calibrated_value_shiftInvariant_restricted` and "**Printed claims
  proved**" to "**Restricted variant proved**"; replace the last sentence ("Lead to decide …") by "Full-support
  π_ref and finite X, Y as in `Eq_DPO_restricted` ([scope](SOURCE-ISSUES.md#statement-index-scope-disclosures))."

## SOURCE-ISSUES scope sentences (append to the RLHF bullet of "Statement-index scope disclosures")

> `eq:reward-policy-eq` (`RLHF.tex:62–66`) and `eq:Jstar` (`:115–124`) are indexed as
> `Eq_reward_policy_eq_restricted` and `Eq_Jstar_restricted`, and the prompt-shift claims of `:90–98` as
> `Eq_calibrated_value_shiftInvariant_restricted`, with the same full-support π_ref and finite X, Y. For the
> prompt-shift claims the printed statements hold for every π_ref under the extended-real KL; the restriction
> comes from the formal KL, which equals the KL divergence only when π_ref has full support.
> `eq:RLHF-policy-closed-form` (`:41–59`) is indexed as `Eq_RLHF_policy_closed_form_restricted`: the Gibbs
> policy π_r maximizes J(r,·) over all conditional policies, and a conditional policy is a maximizer iff it
> agrees with π_r on supp ρ. The printed `π_r := arg max_π J(r,π)` treats the maximizer as unique; that holds
> exactly when ρ has full support (off supp ρ every row gives the same value; machine-checked witness with
> ρ = δ_true in the P3a non-vacuity probe). This is a scope note, not an asserted source error. Same
> full-support π_ref and finite X, Y.

No new SOURCE-ISSUES entry is needed for U13/U14 (disclosed in the docstrings, F1), mirroring `Eq_mdp_value_Q`.

## G2 / import check
`Statements/Ch7.lean` imports (8 lines) are byte-identical to the statement draft header; the body compiles
standalone with exactly those imports (critic run, below). No new G2 edge. New modules are imported only by
`Ch7Proofs.lean` and `Formalization.lean` per the draft coverage notes. Library files import no `Formalization.Statements.*`
other than through `Ch7Definitions → Statements.Ch3Definitions` (pre-existing definitions module).
