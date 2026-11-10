# Critic report: Marl76ZeroSumNEOracle.lean (Theorem 7.6 clause (b) non-vacuity, C45) (2026-11-10)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of `Formalization/MultiAgent/ModelBased/ZeroSumNEOracle.lean` (sha256 079dd2bbff8936d42ea4bcd80ce152c5ff98912368ffeb2d24147f3deed6cff4, 140 lines): a causal exact Nash-equilibrium oracle for two-player constant-sum Markov games, as non-vacuity evidence for clauses (b) and (c) of `Thm7_6_restricted`.

Integration note: verdict ACCEPT-WITH-FIXES; the fixes are docs only and were applied on 2026-11-10. The module is now imported from `Formalization.lean` (the duplicate-declaration clash with `Formalization/MultiAgent/Equilibria.lean` was fixed), so it is covered by the whole-project axiom audit. The proposed wording below was applied to the `Thm7_6_restricted` docstring (Non-vacuity bullet, docstring only), the COVERAGE Theorem 7.6 row (with the file added to its file list), C45 in SOURCE-ISSUES and Erratum 18, and the ledger record's `statement_scope`, `lean_export` and `display_note` (so the site card states the clause (b)/(c) disclosure). Finding 4 (clause (c) also non-vacuous for two-player constant-sum games) is reflected in every wording; the optional `thm7_6_clauseC_hypotheses_constSum` lemma was not added. No status change: Theorem 7.6 stays proved under restrictions. No new statement entry (non-vacuity evidence, not a source result).

Verdict: ACCEPT-WITH-FIXES (fixes are docs only; Lean file accepted as is).

Compile: `bash scripts/lean-local.sh <local probe>` (a copy of the file plus `#print axioms`), exit 0, no errors/warnings, 8.3 s.
All five exports (isNE_margProd_of_isCCE, neOracle_causal, exists_causalNEOracle_constSum, exists_causalNEOracle_zeroSum,
thm7_6_clauseB_hypotheses_constSum) depend on [propext, Classical.choice, Quot.sound] only.

## Findings
1. Game theory (correct, Markov version). For m = 2, `deviate π i π'` gives the product of π' with the other player's marginal of π,
   so bestResponseValueJ G π i s = bestResponseValue G (margProd π) i s. With V₁ = c·H − V₀ on steps 1..H (shift is uniform over
   policies), CCE gives max_μ' V₀(μ'×ν) ≤ V₀(π) ≤ min_ν' V₀(μ×ν'), sandwiching V₀(μ×ν); so equality at every (s,i). Independent
   reconstruction matches the gapJ_shift / gap_margProd_le_two_mul route. Only step-1 conditions are used, matching
   eq:defn-Nash-E / eq:defn-CCE (marl.tex:217–221, 234–238). Constant-sum hypothesis restricted to steps 1..H, consistent with
   the clause's reward hypothesis. Matches the source's own remark (marl.tex:377: NE in two-player zero-sum games via Nash VI).
2. Causality: margProd acts pointwise in (h,s) (Marl77ZeroSum.lean:90); composed with ccePlanner_causal (CausalOracle) gives
   CausalProductOracle. Correct.
3. Clause (b) read exactly: thm7_6_clauseB_hypotheses_constSum restates clause (b)'s two hypotheses verbatim (Ch7.lean:1702–1708)
   and they hold for every N, hN, data since empiricalGame keeps reward := G.reward. Non-vacuous for constant-sum games with
   rewards in [0,1], e.g. r₀ ∈ [0,1], r₁ = 1 − r₀. Builder's point verified: zero-sum (r₀ + r₁ = 0) with both rewards in [0,1]
   forces r₀ = r₁ = 0 on steps 1..H, so the constant-sum form (c = 1) is the meaningful one.
4. FIX (understatement): clause (c) is ALSO non-vacuous for two-player constant-sum games: take One := neOracle hA and
   Occe := ccePlanner hA (ccePlanner_causal, ccePlanner_isCCE for every empirical game). The docs should not say (c) remains
   vacuity-undisclosed for m = 2 constant-sum. Optionally add a one-line `thm7_6_clauseC_hypotheses_constSum`.
5. Remaining open: general-sum m = 2 and all m ≥ 3 (Nash existence not in pinned Mathlib). (m = 1 is plausibly trivial but not
   proved; do not claim it.)
6. Statement entry: no new Ch7 entry needed (this is non-vacuity evidence, not a source result; AGENTS.md entries are per source
   result). Cite the lemma names in the Thm7_6_restricted docstring.

## Proposed wording
Thm7_6_restricted docstring, replace the Non-vacuity bullet:
* Non-vacuity: clause (a) is non-vacuous in Lean (a causal backward-induction CCE planner, `causalCCEOracle_exists`). For
  two-player constant-sum games (`r₀ + r₁ = c` at steps `1..H`, e.g. `c = 1` with rewards in `[0,1]`; strict zero-sum with
  rewards in `[0,1]` forces zero rewards) clauses (b) and (c) are also non-vacuous: the product of the marginals of that planner
  is a causal exact-NE oracle (`exists_causalNEOracle_constSum`, `thm7_6_clauseB_hypotheses_constSum`). For general-sum games and
  for `m ≥ 3` players, clauses (b) and (c) are not shown non-vacuous in Lean: a causal NE oracle there needs Nash's existence
  theorem, which is not in Mathlib.

COVERAGE row (Theorem 7.6), replace "Nash existence is not in the pinned Mathlib, so the NE clauses hold for every causal NE oracle
without a Lean existence proof." with:
"For two-player constant-sum games the NE and joint clauses are also shown non-vacuous (product of marginals of that CCE planner is
an exact NE, Marl76ZeroSumNEOracle.lean); for general-sum or ≥ 3-player games Nash existence is not in the pinned Mathlib, so the NE
clauses hold for every causal NE oracle without a Lean existence proof." (add the file to the file list.)

C45 (lines 16–18), replace "Nash existence ... non-vacuous in Lean." with:
"For two-player constant-sum games the NE and joint clauses are also non-vacuous in Lean (the product of the marginals of that
planner is a causal exact Nash equilibrium oracle, `exists_causalNEOracle_constSum`). For general-sum two-player games and games
with three or more players, Nash existence is not in the pinned Mathlib, so the NE and joint clauses are proved for every causal NE
oracle but not shown non-vacuous in Lean."
