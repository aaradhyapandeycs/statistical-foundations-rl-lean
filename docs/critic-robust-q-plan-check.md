# CHECK: robust history-optimal / robust Q plan (independent plan checker, refutation stance)

Public copy of the independent plan check; local paths removed. The plan checked here is the builder's private plan; it is not published.

Post-review note (added to this public copy, 2026-11-08): only the stationary printed claim (Fix 1, Fix 7) was built; the optional history-dependent strengthening was not started. Fix 5 suggested a separate definitions file; to respect the frozen import-layering gate, `robustPolicyQ` was instead placed in the existing definitions-only module `Formalization/RobustRL/Ch7/Ch7Definitions.lean` (which keeps Fix 5's requirement that the statement file import definitions modules only); the proofs are in `Formalization/RobustRL/DRVI/RobustQ.lean`, and the entry is `Eq_mdp_value_Q` in `Formalization/Statements/Ch7.lean`. The check text below is otherwise unchanged.

Date: 2026-11-08. No Lean or lake was run, nothing was fetched, and nothing under `Formalization/` was touched.
Plan sha256 verified: `c36cb827e0a174836818f4612482f5ec456fbe630e6e67a5c3652689ec741400` (matches the brief).
I read the following before reading the plan's conclusions: `robust_RL.tex:20–110` and `prelim.tex:55–85` (the plan's source hashes were not re-hashed),
`DRVI/Optimality.lean` (all of it), `DRVI/PolicyEvaluation.lean:180–260`, `DRVI/RowSets.lean:20–45`,
`Ch7/Ch7Definitions.lean:30–135`, `MDP/InfiniteTrajectory.lean`, `MDP/InfiniteReturn.lean` (defs, limit lemma),
`MDP/ForcedActionTrajectory.lean`, `MDP/ForcedActionReturn.lean`, `Statements/Ch7.lean` (def list), and `Statements/Ch5.lean`
(naming precedent). I checked the Mathlib names in a read-only Mathlib checkout at the same pinned rev, `32d24245`.

## Verdict: GO WITH FIXES

The mathematics is correct. The plan reads the source correctly, and the Lean design is feasible. The fixes concern what the
statement-index entry may contain and its name, plus one non-vacuity gap in the history clauses.

## Answers to the five checks

### (1) Reading
- **Adversary.** `:76–84` defines `V^{π,σ}(s) = inf_{P∈U^σ(P^0)} V^{π,P}(s)` with `V^{π,P}` the value "in the standard MDP with
  transition kernel P". So one complete kernel is chosen for the whole trajectory (static adversary). The book defines no
  dynamic or time-varying nature. Confirmed. The Lean `robustPolicyValue` (`Ch7Definitions.lean:76`) uses the same reading.
- **Policy class.** The only policy definition is `prelim.tex:66` ("a stationary policy π: S → Δ(A)", randomized allowed).
  `:76` remarks that time-invariant policies typically suffice. The robust chapter introduces no other class. So the
  printed `max_π` ranges over stationary randomized policies. Confirmed.
- **History-dependent version.** This is a disclosed strengthening, not a correction, and it needs no SOURCE-ISSUES entry.
  Caveat: Iyengar (2005), the paper the book cites, is set against a dynamic or rectangular nature, so the static-adversary
  history theorem is not literally "the cited theorem" either. COVERAGE should say "history-dependent strengthening under the
  book's static adversary" (the plan's §8.6 already says this). The prove-cited-results rule is satisfied by the printed
  claim, because the book cites the result for exactly that claim. The history clause is optional extra value, not a
  requirement for closing D13.

### (2) Truth (re-derived)
- Fix `U` = the ball family, `V⋆ = optFix`, and `K⋆ = worstKernel U hU V⋆`. By rectangularity, `K⋆` is admissible
  (`worstKernel_mem`). For **every** `(x,a)`:
  `r(x,a) + γ⟨K⋆_{xa},V⋆⟩ = r + γ·rowInf(U x a)V⋆` (`worstKernel_spec`) `= robustQ V⋆ x a ≤ actionMaximum = optOp V⋆ x = V⋆ x`
  (`optFix_spec`). This holds for all `a` because `worstKernel` is defined row by row for every `(s,a)`. It is not
  restricted to the greedy action. (Indeed `max_a` gives equality, so `V⋆` is exactly the optimal value of the ordinary MDP
  `K⋆`.)
- For a history policy π: `inf_P V^{π,P}(s) ≤ V^{π,K⋆}(s) ≤ V⋆(s)` (ordinary-MDP supersolution bound) `= V^{π⋆,σ}(s)`
  (existing). The argument is the min-max ≤ max-min step, and it only needs `K⋆` to be one admissible static kernel. It is
  correct.
- Q with a forced first action: `Q^{π,K⋆}(s,a) = r(s,a) + γ E_{s'∼K⋆_{sa}}[continuation from (s,a,s')]`. The continuation is
  a history policy value in the MDP `K⋆` and is at most `V⋆(s')`. So `Q ≤ robustQ V⋆ s a`. Correct. This holds for any
  continuation, so the bound does not depend on how the continuation is read (see Q2 below).
- Attainment. Only `RowAttains` of every row at σ ≥ 0 is used: `tvBall_rowAttains` and `chiBall_rowAttains`
  (`RowSets.lean:160,186`), lifted at `Optimality.lean:183–189`. `RowAttains.nonempty` gives nonempty rows, which supplies
  `optFix_bounds` and the nonempty sInf sets. No compactness beyond that is used.
- Measurability. Everything sits on finite types with `⊤` σ-algebras. The history kernels use `Kernel.ofFunOfCountable` on
  `Iic n → A×S`, which is countable with measurable singletons; the stationary file already uses this route successfully.
  I found no hidden subtlety.
- sInf junk values. `robustHistoryValue` and `robustHistoryQ` are sInf of sets that are nonempty (`K⋆`, or the nominal kernel)
  and bounded below by 0. `csInf_le` therefore needs only the `BddBelow` bound (by 0), which the plan budgets.

### (3) "The printed claim only lacks the Q half"
**Confirmed.** The value half, exactly as printed (simultaneous across states, with one deterministic `f`), follows from two
exports: `robustOptimalValue_eq_robustPolicyValue_optPolicy`, a function equality with a single
`f = optPolicy (ballFamily ball M σ) M`, and the domination and attainment in `familyOptimal_eq_optFix`
(`IsGreatest.csSup_eq`) or `HorizonTrap.robustPolicyValue_le_optimal`. Both take `hU`, which is discharged from σ > 0 via the
row-attainment lemmas. The repository has no robust Q of a policy (`Q^{π,σ} = inf_P Q^{π,P}`) and no index entry, so the
printed claim as a whole is **not** yet covered. D13 of the private triage ledger ("Proved for stationary policies") overstates the coverage.
D13 needs re-grading (see Q7).

L5 re-derived:
- `≥`: `Q^{π⋆,K} = r + γ⟨K_{sa},V^{π⋆,K}⟩ ≥ r + γ⟨K_{sa},V⋆⟩ ≥ robustQ`. This uses `V^{π⋆,K} ≥ V^{π⋆,σ} = V⋆` pointwise and the
  fact that `K_{sa}` is a probability vector.
- `≤`: at `K⋆`, `V^{π⋆,K⋆} = V⋆`. Use the `hKw` part of `familyRobustValue_eq_policyFix` after rewriting `policyFix_optPolicy`,
  so `worstKernel (policyFix π⋆) = worstKernel optFix`.
- Stationary domination: `V^{π,K⋆} ≤ V⋆` follows from the ordinary policy-evaluation comparison.

All three steps are sound.

### (4) The proposed entry
- **Name.** Do not use `Claim7_mdp_value_Q`. In this index, `ClaimN_k` denotes a *numbered* `claim` environment
  (`Claim5_1_corrected` is `claim:PV-l-UB`, "Claim 5.1"). `Claim7_…` would suggest a nonexistent "Claim 7.x". Unnumbered
  displays use a label-derived name (Ch5 precedent: `MVP_optimism_corrected` for `eq:optimism-Q-V-geq-mvp`). COVERAGE records
  such displays as "displayed claim, no named-ledger entry". Suggested name: `Eq_mdp_value_Q`, mirroring `eq:mdp-value-Q`.
  The lead decides. Whichever name is chosen, the docstring must say "unnumbered display" and give `robust_RL.tex:88–98`.
- **Should it be indexed?** Yes. AGENTS.md requires an entry for every result COVERAGE records as proved, and Ch5 indexes
  displayed claims. The COVERAGE row must say it adds no numbered-ledger entry.
- **Contents.** Per AGENTS.md, "The entry states the printed result". The printed entry should contain clauses (i) only:
  stationary value and stationary Q, with one `∃ f` (see Fix 1).
- **Quantifier order.** `∀ State Action M σ (0<σ) ball, ∃ f, …` is right: π⋆ may depend on the RMDP but not on `s` or `(s,a)`.
  One `f` for both V and Q matches the display, which names a single `π⋆` for both halves. This is stronger than a
  "resp." reading and is true.

### (5) Lean design
- `Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure` **exists** at the pinned rev
  (`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean:775`; `{a : ℕ}` implicit; it needs `[IsProbabilityMeasure μ₀]` from
  section variables). It is already used verbatim at `InfiniteTrajectory.lean:155`.
- `Measure.integral_compProd` exists (`Kernel/Composition/IntegralCompProd.lean:473`, `Integrable f (μ ⊗ₘ κ)` hypothesis).
- The `HistoryPolicy` indexing is consistent. `κ n : (Iic n → A×S) → A×S` produces pair `n+1 = (a_{n+1}, s_{n+2})`; the
  current state is `(h n).2 = s_{n+1}`; `s₀` is a parameter and not part of the history. This matches `trajectoryState`
  (`| n+1 => (path n).2`).
- Supermartingale bookkeeping re-derived. With `F_n = partial(n+1) + γ^{n+1}V((path n).2)`,
  `F_{n+1} = F_n − γ^{n+1}V(cur) + γ^{n+1}r(cur,a_{n+1}) + γ^{n+2}V(s_{n+2})`. The inner integral under `κ_n(h)` is
  `≤ F_n(h)` by the supersolution inequality at `cur` with the action mixture `next(h)`. Correct.
- Generic limit lemma. The proof of `tendsto_integral_partialDiscountedReturn` (`InfiniteReturn.lean:138–151`) uses the
  measure only through `integrable_const`, so a version for any finite or probability measure is a direct copy. Agreed.
- Measurability of `G` on the countable marginal type: use `DiscreteMeasurableSpace` (countable plus singleton) or the
  plan's `integral_fintype` fallback. Either works.
- L1 (ofStationary laws) is **not needed** for the four printed or strengthened upper-bound clauses. It is needed for
  non-vacuity (Fix 2) and for the sSup corollary. Keep it, but schedule it as mandatory for Fix 2, not as an optional
  extra.
- Size. 0.75–1.2k lines is realistic. L3 is the risk: the compProd and `Iic` index bookkeeping could exceed 450 lines,
  so budget up to about 600. The stationary-only printed claim (`robustPolicyQ` plus L5 plus the entry) at 150–300 lines is
  realistic.

## Required fixes (numbered)

1. **The printed entry states the printed claim only.** Put the stationary value and stationary Q clauses (plan clause (i))
   in the main entry. Move the history-dependent clauses (ii) to either (a) a library theorem only, recorded in COVERAGE as a
   strengthening, or (b) a separate, clearly named entry (for example `Eq_mdp_value_Q_historyDependent`). Its docstring
   would say "strengthening beyond the printed claim (book defines only stationary policies, prelim.tex:66); static
   adversary as in :76–84; not a correction". Do not fold strengthening clauses into the printed entry, and do not use the
   `_corrected` or `_restricted` suffixes.
2. **Non-vacuity of the history clauses.** As planned, clauses (ii) are upper bounds only. A wrong or degenerate
   `historyValue` (for example a mis-indexed kernel, or junk ≡ 0) would satisfy them trivially, and they never state that
   the maximum over history policies is attained. Wherever (ii) is stated, add the identities
   `∀ π s, robustHistoryValue ball M σ (HistoryPolicy.ofStationary π) s = robustPolicyValue ball M σ π s` and
   `∀ π s a, robustHistoryQ ball M σ (ofStationary π) s a = robustPolicyQ ball M σ π s a`. These come from L1 plus `withKernel`
   congruence. They make "attained by `ofStationary (detPolicy f)`" explicit and anchor the semantics. Prove L1 at the
   **law** level, not just at the value level.
3. **Rename** `Claim7_mdp_value_Q` to a label-derived name such as `Eq_mdp_value_Q` (see (4)). The docstring should say
   "unnumbered display `eq:mdp-value-Q`, `chapters/robust_RL.tex:88–98`" and cite the definitions at `:24–52`, `:76–84` and
   `prelim.tex:66`. COVERAGE should say "displayed claim; no numbered-ledger entry".
4. **Ball quantification.** Replace `∀ ball ∈ ({tvBall, chiBall} : Set (RowBall State))` with two explicit conjuncts (TV, χ²)
   or `∀ ball, ball = tvBall ∨ ball = chiBall → …`. This is more readable and avoids set-literal elaboration over `RowBall`.
   Use universe-polymorphic carriers (`Type u`, `Type v`) as the other entries do, or document why `Type` suffices.
5. **Definition placement.** `robustPolicyQ` (stationary) is not a history object. Put it in a separate definitions file (for
   example `RobustRL/Ch7/RobustQDefinitions.lean`) or name the planned file neutrally. Every module the statement file
   imports must hold definitions and instances only, with no proved lemmas beyond instance obligations.
6. **Triage-ledger and COVERAGE wording.**
   - Re-grade D13: the printed claim is NOT fully covered. The value half is proved (stationary). The Q half is open, small
     (about 150–300 lines), and is the priority. The history-dependent strengthening is optional.
   - Correct D13's text "Proved for stationary policies", because the Q half is missing.
   - The plan's line "π⋆ also attains V⋆ [against the dynamic adversary]" is unproved. Do not put it in COVERAGE.
7. **Sequencing.** Land the stationary printed entry (L5 plus Fix 1) first, as an independent unit that Builder B can do
   without Builder A. Index the history entry only after L1–L4 and Fix 2 compile and a critic has reviewed them.

## Answers to the plan's open questions

1. Yes. The stationary randomized class is the printed reading, and the history version is a disclosed strengthening. The
   entry carries the stationary clauses only (Fix 1). Do not make the entry history-only, because that would not let a
   reader check it against `prelim.tex:66`.
2. Yes. "Force `a_0 = a`, then continue π with `a_0` in its history" is the standard `Q^π`. Restarting π after `a` is a
   different object that is not standard. The upper bound holds for any continuation anyway; the reading matters only for
   the ofStationary identity (Fix 2), where `forceFirst ∘ ofStationary` matches `forcedActionTrajectoryLaw` (same
   `historyKernel π`).
3. Static adversary confirmed (`:78`, "standard MDP with transition kernel P"). Do not index a dynamic-nature version.
4. Confirmed for all `a`. Only row-wise attainment from `worstKernel_spec` and `RowAttains` at σ ≥ 0 is used, with no extra
   compactness. Without attainment, ε-worst kernels would work; that is not needed here.
5. Yes. One `∃ f` before all conjuncts is right. It is also right for Fix 1's split: each entry has its own `∃ f`, and the
   history entry should state that its `f` is the same one, or restate the stationary clauses.
6. No objection. `chiBall = qChiBall` (support condition `q ≪ p`) agrees with the finite-χ² requirement of `eq:defn-chi2`.
   TV with σ ≥ 1 is the whole simplex and is harmless. Keep σ > 0 as printed.
7. Yes. Re-grade D13 as in Fix 6: printed claim partially covered (Q half open); history strengthening optional.
