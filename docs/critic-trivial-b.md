# CRITIC: trivial batch B (Ch7): independent review

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-09): this critic reviewed the pre-integration snapshot; the four entries were integrated into the library on 2026-11-08/09. R1 was applied before landing: the `Eq_DPO_restricted` docstring, the `eq:DPO` row of `COVERAGE.md` and the scope-disclosure bullet in `SOURCE-ISSUES.md#statement-index-scope-disclosures` say that over all policies the minimum 0 can be attained only at boundary (non-Gibbs) policies, while over full-support policies the infimum 0 is unattained and no reward MLE exists. F1 was folded into that scope-disclosure bullet; no new source-issue number was opened. F3: no named-result ledger records were added (displays and remarks are not counted). F4: this file is the critic copy linked from the ledgers. Snapshot files map to the integrated locations as follows: `VPOReparam712.lean` → `Formalization/Ch7Rest/VPOReparam712.lean`; `OraclePlannerChi.lean`, `OraclePlannerChiNumerics.lean`, `OraclePlannerChiMain.lean` → the files of the same names in `Formalization/RobustRL/DRVI/`; `StatementsVPO.lean` and `StatementsRemark72.lean` → the entries in `Formalization/Statements/Ch7.lean`; `StatementsVPOProofs.lean` and `StatementsRemark72Proofs.lean` → the `_holds` wrappers in `Formalization/Statements/Ch7Proofs.lean`. `CHECK` items refer to the independent plan check, published as `critic-trivial-batch-plan-check.md`; the plan itself and the builder's notes (DRAFTS, STATUS) are private and not published. Short file names below refer to the reviewed snapshot files, and the file hashes are those of the snapshot. The review text below is otherwise unchanged.


Date: 2026-11-08. Reviewer: independent critic. I did not build these entries. I read the source first (`RLHF.tex:21–198`,
`robust_RL.tex:437–457`), then the plan §2, CHECK (X1, X2, B1-a, B2-a, B4-a), the snapshot, and the builder notes.
No paper was fetched. Nothing under `Formalization/`, `docs/` or the builder WIP was edited. Lean was run only through
`bash scripts/lean-local.sh`, in the foreground, one compile at a time.

## 0. Pins

- Snapshot (the builder's read-only pre-integration snapshot, private): all 8 sha256 match the builder's snapshot hash list. The
  builder's live working files are byte-identical to the snapshot (`cmp`).
  - OraclePlannerChi c8be5efd…, OraclePlannerChiMain 7bc1d68a…, OraclePlannerChiNumerics 72971656…,
    StatementsRemark72 89602601…, StatementsRemark72Proofs e3c6322d…, StatementsVPO 79c45e84…,
    StatementsVPOProofs 84e58ef0…, VPOReparam712 f847103b…
- Source: RLHF.tex e60115c3…, robust_RL.tex 95ce19a9… (these match the hashes in the plan table).
- Builder notes: DRAFTS-FOR-LEAD.md 00c08664…, STATUS.md 4a410450…, axiom-probe.out 60229d53…
- Plan 4ecd6180…, CHECK 7f089b33…
- Critic probes (reviewer's private probe folder): `CriticProbe.lean` 25a4ae3a…, `CriticProbeB4.lean` 4e8063ae….

## 1. Independent rebuild and axioms

I did not trust the builder's oleans. I copied the snapshot to the reviewer's private probe folder, changing only the
import prefix (builder's working prefix → reviewer's private prefix). Files without such imports are byte-identical to the snapshot. I then
compiled each module in dependency order with
`bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean <probe folder>/<X>.lean`.
All 8 modules exited 0 with no output (build log in the reviewer's private probe folder).

`CriticProbe.lean` (exit 0, output kept in the reviewer's private probe folder) runs `#print axioms` on the four `_holds`,
`chi_oracle_planner_guarantee`, `chi_oracle_planning_bounds`, `chi_selfBoundExpr_le_of_planning`,
`chi_good_gap_of_valueGap`, `online_vpo_step`, `dpo_argmin_iff` and `vpo_argmin_iff`. Every one reports exactly
[propext, Classical.choice, Quot.sound], which agrees with the builder's `axiom-probe.out`.

Forbidden tokens: none found. The grep covered sorry, admit, axiom, native_decide, maxHeartbeats, #eval, #check,
#print, implemented_by, extern, unsafe, opaque, private paths and TODO. No library module imports
`Formalization.Statements.*` (X1 holds). Each wrapper applies a library theorem: B1 is a direct term, and B2–B4 are
tuple or `exact` applications of `dpoLoss_gibbs`, `exists_gibbsPolicy_eq`, `gibbsPolicy_eq_iff`, `dpo_argmin_iff`,
`vpoObjective_gibbs_optCal`, `vpo_argmin_iff`, `calShift_eq_neg_kl`, `vpoObjective_calSwap` and `online_vpo_step`.
No wrapper restates or re-proves a result.

## 2. Verdicts

| Entry | Verdict |
|---|---|
| `Eq_DPO_restricted` | **ACCEPT WITH DISCLOSURES**, conditional on R1 (a docstring and ledger wording fix; the Prop is unchanged) |
| `Eq_policy_RBMLE_restricted` | **ACCEPT WITH DISCLOSURES** |
| `Eq_online_RBMLE_restricted` | **ACCEPT WITH DISCLOSURES** |
| `Remark7_2_restricted` | **ACCEPT WITH DISCLOSURES** |

## 3. Per-entry review

### B2 `Eq_DPO_restricted` (RLHF.tex:62–74, :90)

- **Fidelity.** `dpo` transcribes `eq:DPO` (:68–72) exactly. `nll` is ℓ(r,D) (:37–39). The dataset is a `List`,
  so duplicates are allowed, which is fine.
  - (i) says Z cancels (:74).
  - (ii) is `eq:reward-policy-eq` (:63–66).
  - (iii) is the prompt-shift identifiability (:90), stated as a two-sided iff.
  - (iv) is the argmin correspondence, with `∀ π, IsPositivePolicy π →` outside the iff. Its left side is
    "minimal among full-support policies".
  - Quantifiers: `∀ X Y π_ref β D`, then `π_ref > 0` and `β > 0`. Correct.
- **Junk values.** Every policy that is evaluated has full support. The Gibbs policies are positive
  (`gibbsPolicy_isPositive`), so `log 0 = 0` is never reached. With `Y` empty, `IsPositivePolicy π_ref` is false
  (because 0 ≠ 1), so the entry is vacuous only in a degenerate case where no policy exists. Division by `π_ref` is
  safe because `π_ref > 0`.
- **Restriction is substantive and disclosed.** It applies to the argmin over full-support policies, to a
  full-support `π_ref`, and to finite `X` and `Y`.
- **R1 (blocking for landing; text only).** The docstring sentence below is self-contradictory as written. The same
  sentence appears in the DRAFTS COVERAGE row and in the SOURCE-ISSUES bullet:

  > "in the source's extended-real reading a policy with π(y₋|x) = 0 has −log σ(+∞) = 0, so over all policies the
  > DPO infimum can be 0 and unattained while every full-support policy has positive loss"

  Take D = [(x,y₁,y₂)]. In the extended-real reading, any policy with π(y₂|x) = 0 and π(y₁|x) > 0 has loss 0, so
  over all policies the infimum 0 is **attained**. It is unattained only over full-support policies. In that case
  the printed argmin over all policies is a set of boundary (non-Gibbs) policies, while the restricted argmin and
  the set of reward MLEs are both empty.

  Suggested replacement: "in the source's extended-real reading a policy with π(y₋|x) = 0 has −log σ(+∞) = 0, so
  over all policies the minimum 0 can be attained only at boundary policies, which are not Gibbs policies, while
  over full-support policies the infimum 0 is unattained and no reward MLE exists (e.g. a dataset whose only
  comparison is (x, y₁, y₂))". In Lean, `log 0 = 0` gives such a policy the junk loss −log σ(β log(π(y₁)/π_ref(y₁)))
  instead of 0.

  The CHECK text B2-a contains the same slip, and the builder copied it.
- F1 (non-blocking). The example also shows that the printed equivalence "MLE ⇒ π_DPO" can fail at the boundary.
  The printed argmin exists while r_MLE does not. The lead may decide whether this is a scope disclosure (the
  current plan) or deserves a SOURCE-ISSUES note.

### B3 `Eq_policy_RBMLE_restricted` (RLHF.tex:115–141)

- **Fidelity.**
  - (i): `vpoObjective` with coefficient `sign·α` is DPO + sign·αβ E_{ρ,π_cal}[log π − log π_ref], which is the
    last line of `eq:policy_RBMLE` (:131–132). Its value at π_r equals ℓ(r,D) − sign·α·J⋆(r;π_cal) (:126–128).
    This follows from J⋆ = −β E[log π_r − log π_ref] (`eq:Jstar`). Correct.
  - (ii): the argmin correspondence (:126–133). Correct.
  - (iii): the KL identity (:138–139). It holds for π > 0 and π_cal ≥ 0, and terms with π_cal = 0 vanish on both
    sides (`klDiv` uses p·log(p/q)), so it is not a junk artifact.
  - (iv): `∃ K, ∀ π`, so K is chosen before π. The witness in the wrapper is
    K = sign·αβ Σρ Σπ_cal(log π_cal − log π_ref), which is independent of π. I re-derived it:
    log π − log π_ref = (log π − log π_cal) + (log π_cal − log π_ref). The inline DPO part is syntactically the
    same as `vpoObjective`'s. When π_cal(y) = 0, the `log π_cal` junk is multiplied by 0, so it is harmless.
- **J⋆ through `sSup`.** I checked for junk. `optCalValue` is turned into the closed form by the library lemma
  `optCalValue_eq`, which uses IsGreatest under ρ ≥ 0 and π_ref > 0. So the supremum is attained and is not the
  `sSup` junk value 0. ρ is not required to sum to 1. That is more general than the source and harmless.
- No issues.

### B4 `Eq_online_RBMLE_restricted` (RLHF.tex:158–198, :177)

- **Fidelity.**
  - (a): B4-a is satisfied. The objective is the printed **uncalibrated** J(r,π) = Σρ(Σπ r − β KL(π‖π_ref)) of
    `eq:KL_reward` (:42–44), written inline. It is maximized over all `IsCondPolicy π` (the closed simplex), as in
    `eq:RLHF-policy` (:172–175). The convention KL with 0·log 0 = 0 is the correct one, not junk.
  - (b): `IsVPOMinimizer` with α corresponds to sign = +1. It is `eq:online_RBMLE` (:194–198) for an arbitrary D,
    which covers D^{(t)}. The off-by-one between the source's D^{(t)} and the algorithm's index does not matter,
    because D is arbitrary.
  - Uniqueness and existence are not claimed, and both omissions are disclosed.
- **Non-vacuity, machine-checked.** The minimality hypothesis `∀ r', obj r ≤ obj r'` is not always satisfiable,
  because C44 shows the online objective can be unbounded below (for example, D = []). `CriticProbeB4.lean`
  (exit 0, no output) proves that a minimizer exists in a concrete instance. The instance: X = Unit, Y = Bool,
  π_ref = π_cal uniform, ρ = 1, α = β = 1, D = [(⋆,true,false),(⋆,false,true)]. There r = 0 minimizes, since
  obj r = log(2(eᵃ+eᵇ)) − (a+b)/2 ≥ 2 log 2 = obj 0 by AM–GM. So the entry is not vacuous.
- F2 (non-blocking). The converse direction is not restated in B4: every full-support VPO minimizer is π_r for a
  minimizer r. B3 (ii) with sign = 1 supplies it. This is acceptable.

### B1 `Remark7_2_restricted` (robust_RL.tex:453–457; Thm 7.4 :437–450)

- **Fidelity.**
  - Quantifiers are `∀ c_opt ≥ 0, ∃ c₂ > 0, ∀ S A M σ δ ε N hN`, as required. The premises match
    `Thm7_4_corrected` (Ch7.lean:468) line by line: σ > 0, 1/4 ≤ γ (γ < 1 comes from the structure), δ ∈ (0,1),
    ε ∈ (0, 1/(1−γ)], and the sample-size condition with log(SAN/δ). The T and greedy-pick quantifiers are
    correctly dropped.
  - The requirement is `|V̂⋆(s) − V̂^{det f}(s)| ≤ c_opt/N²·log(SAN/((1−γ)δ))` for every s. This is the printed log
    argument (:456).
  - Outputs: deterministic only, and this is disclosed. The event is uniform over f, and the docstring says so.
  - The docstring states the witness as c₂ = 10⁶ + 8c_opt, which matches the proof.
  - The paper claim "∃ c₂ ∀ c_opt is false" is correct. A huge c_opt admits every deterministic f, because the
    gap is at most 1/(1−γ). On an MDP with an action gap greater than ε, the event then has probability 0.
- **Non-vacuity, machine-checked.** `CriticProbe.lean` proves that for every data set the exact empirical robust
  optimal deterministic policy `optPolicy (ballFamily chiBall M̂ σ) M̂` meets the requirement for every c_opt ≥ 0.
  The proof uses `robustOptimalValue_eq_robustPolicyValue_optPolicy`, and the log argument is ≥ 1. So the
  requirement is attainable and the event is not vacuous.
- **Numerics, checked.**
  - `chi_oracle_planning_bounds` assumes c₂ ≥ 8c_opt, L' ≥ 1/2, L ≤ L' + 1/(1−γ), and the sample condition. It
    concludes Ξ ≤ 1 and Ξ/(1−γ) ≤ ε/2. Internally it shows c_opt·L'/(N²g) ≤ ε/8 and c_opt/(N²g²) ≤ ε/4, so
    Ξ/g ≤ 3ε/8.
  - This avoids the plan's √(8c_opt)/log 2 term by using c_opt/2 ≤ c_opt·L' ≤ N g³ε²/8, which is valid.
  - `chi_selfBoundExpr_le_of_planning` takes `Ξ ≤ 1` (giving 1 + Ξ ≤ 2 inside the square root, per B1-a) and
    `Ξ/(1−γ) ≤ ε/2`, and concludes `2·selfBoundExpr + Ξ/(1−γ) ≤ ε`.
  - The term bounds proved inside it are t1 ≤ 0.072ε, t2 ≤ 1.44e-4ε, p1 ≤ 1e-6ε, p2 ≤ 0.006ε, p3 ≤ 1.2e-5ε,
    p4 ≤ 0.048ε and p5 ≤ 2.4e-5ε. Their sum is about 0.1262ε ≤ ε/2. This confirms the "≈ 0.126ε" claim and the
    docstring's "below 0.13ε".
  - L ≤ L' + 1/(1−γ) is `chi_log_shift`, using log x ≤ x − 1.
  - The main proof splits on |A| ≤ 1 rather than SA = 1. That is legitimate: a subsingleton Action gives f = π⋆.
    Otherwise SA ≥ 2 and `chi_L_lower` applies.
  - The `|·|` versus one-sided reading of the requirement is disclosed, and the planner only uses the one-sided
    bound (`le_abs_self`).
- No issues.

## 4. DRAFTS-FOR-LEAD.md ledger text

- §1 file map, imports and the X1 list: accurate. Ch7.lean already imports `VPODefs712` and `Ch7Definitions`. The
  section-local instance `ch7StatementStateMeasurable72` exists at Ch7.lean:421, so dropping the WIP copy is
  correct. The two Ch7Proofs imports listed are the ones needed.
- §2 COVERAGE rows: accurate, except that the `eq:DPO` row repeats the R1 sentence. Fix it with R1.
- §3 named-result-status: no rows proposed. The precedent (PROGRESS.md line 25, Remark 7.1) is confirmed.
  **F3:** CHECK X2 literally asked for `named-result-status.json` rows for every entry. The builder deviates and
  justifies it by precedent. This is the lead's call; I see no fidelity problem.
- §4 SOURCE-ISSUES bullets: accurate, except the R1 sentence.
- §5 PROGRESS row. **F4:** it names the critic output `docs/critic-trivial-batch-b.md`. This review is published as
  `critic-trivial-b.md`. Update the row, or copy the file there, at integration.
- The `Thm7_4_corrected` docstring still says "Not covered: the oracle-planner Remark (:453–457)". Update it when
  B1 lands, as DRAFTS suggests.

## 5. Items

- **R1** (blocking, text only): correct the "over all policies the DPO infimum can be 0 and unattained" sentence in
  three places: the `Eq_DPO_restricted` docstring, the DRAFTS §2 `eq:DPO` row, and the DRAFTS §4 bullet. The Prop,
  the proofs and the olean contents are unaffected (only the docstring changes).
- **F1:** boundary minimizers versus MLE non-existence for `eq:DPO`. Consider a SOURCE-ISSUES note in addition to
  the scope disclosure (lead's call).
- **F2:** B4 omits the converse argmin direction. B3 (ii) covers it. Acceptable.
- **F3:** named-result-status rows are omitted against the literal text of X2. Justified by precedent; lead's call.
- **F4:** the critic file path in the DRAFTS §5 PROGRESS row is wrong.

## 6. Commands run

- `shasum -a 256` (snapshot, live, source, notes); `cmp` live against snapshot.
- 8 times: `bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean <probe folder>/<X>.lean`
  (all exit 0).
- `bash scripts/lean-local.sh <probe folder>/CriticProbe.lean` (exit 0; axioms
  plus B1 non-vacuity).
- `bash scripts/lean-local.sh <probe folder>/CriticProbeB4.lean` (exit 0 after
  one glue fix; B4 non-vacuity).
- Not run: lake, `scripts/check.py`, `Audit.lean`, or full-tree integration. Those are left to the lead.

Artifacts left in place: the reviewer's oleans under the project build folder, which are project-local critic artifacts the
lead may delete.
