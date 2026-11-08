# CRITIC: robust-RL displayed claim `eq:mdp-value-Q` (robust_RL.tex:88–98)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this review covered the builder's pre-integration snapshot. To respect the frozen import-layering gate (no new import edge from `Formalization/Statements/Ch7.lean`), the definition `robustPolicyQ` was not integrated as a separate `RobustQDefinitions` module: it was appended, with a byte-identical body, to the existing definitions module `Formalization/RobustRL/Ch7/Ch7Definitions.lean`, which the statement file already imports. The proof module was integrated as `Formalization/RobustRL/DRVI/RobustQ.lean`, unchanged except for its import (now `Formalization.RobustRL.Ch7.Ch7Definitions`) and the F2 docstring citation fix. The draft entry and wrapper became `Eq_mdp_value_Q` in `Formalization/Statements/Ch7.lean` and `Eq_mdp_value_Q_holds` in `Formalization/Statements/Ch7Proofs.lean`; on integration the docstrings were changed to address F1, F2, F4 and F5. Short module names below (RobustQDefinitions, RobustQ, Statement, StatementProofs) refer to the reviewed snapshot files; the file hashes quoted below are those of the reviewed snapshot. The review text below is otherwise unchanged.

Date: 2026-11-08. Independent critic (did not build). Nothing under `Formalization/` or the builder WIP dir was edited;
no lake / lean-lsp; one foreground `scripts/lean-local.sh` run (probe, no `-o`). No paper fetched.

## Verdict: ACCEPT WITH DISCLOSURES

The entry states the printed claim (stationary randomized policies, static adversary, both balls, σ > 0) and
`Eq_mdp_value_Q_holds` proves it from library theorems with only the standard axioms. The disclosures below are
wording and coverage notes. None is a source issue and none needs a SOURCE-ISSUES entry.

## Hashes

Source read first: `robust_RL.tex` sha256 `95ce19a9…6d9` (lines 20–120), `prelim.tex` sha256 `2d27bb72…31a5`
(lines 55–75, 115–126).

Snapshot = live = the builder's snapshot hash list (verified with `shasum -a 256`, all four identical):

```
136e8f10f2651dfb78a83892775363d282719f97d3c29fb3717be709836b6e44  RobustQ.lean
7f1b4bf6c5442aa9701bda729d18fef5770d121ca67fe55be27c48e8f16f7b12  RobustQDefinitions.lean
2075f5ccbd93ab51933032d6b8e45e3a1713b014b31423f3431836a88b908fa7  Statement.lean
616246441e2f3f956a6411f502b0887ed680f226abb1b05fece01d9ddc73b723  StatementProofs.lean
```

Probe: `Probe.lean` in the reviewer's private probe folder (sha256 `406a2697a3779f97c0846e382c0b49768a4dbdf493f12da505e90b022b955dfb`),
output `probe.out` in the same folder. Command:
`bash scripts/lean-local.sh <reviewer probe folder>/Probe.lean`. Exit 0, 6 s, no errors or warnings.

## 1. Statement fidelity (`#print`, with universes, checked)

| Source element | Lean | Finding |
|---|---|---|
| σ > 0 (`:41`) | `0 < σ →` | As printed. The library uses only σ ≥ 0, and the wrapper passes `hσ.le`, so the library assumes less. This is not a discrepancy. |
| TV, `eq:TV` (sup over events) | `tvBall`: half-L1 ≤ σ | On a finite carrier the two are equal. This is the existing convention (Lemma7_1). |
| χ², `eq:defn-chi2`, defined only for P ≪ Q; ρ(P_{sa}, P⁰_{sa}) = χ²(P_{sa}‖P⁰_{sa}) | `chiBall p σ = qChiBall p σ` = {q \| p x = 0 → q x = 0} ∧ Σ_{p x>0} (q x − p x)²/p x ≤ σ | Direction is correct: ∫(dP/dP⁰−1)² dP⁰ = Σ (q−p)²/p. The set is support-aware (q ≪ p), so a zero denominator gives no free mass. |
| (s,a)-rectangular U^σ(P⁰) = ⊗ U^σ(P⁰_{sa}) (`:39–48`) | `RobustAdmissible`: ∀ s a, K s a ∈ ball (P⁰ s a) σ | Exact. |
| V^{π,σ}(s) = inf_{P∈U} V^{π,P}(s) (`:76–79`) | `robustPolicyValue` = sInf of actual trajectory values over admissible complete kernels | Static adversary: one kernel for the whole trajectory, as at `:78`. |
| Q^{π,σ}(s,a) = inf_{P∈U} Q^{π,P}(s,a) (`:80`) | `robustPolicyQ` = sInf of `(withKernel M K).trajectoryExpectedQ π s a` | `trajectoryExpectedQ` integrates the infinite discounted return under `forcedActionTrajectoryLaw` (first action forced to `a`, π afterwards). This is `defn:Qpi-inf-horizon` (prelim.tex:115–123). It matches the source. |
| policy class of max_π (`prelim.tex:66`) | `StationaryPolicy = State → FiniteDistribution Action` | Randomized stationary policies, as printed. |
| "∃ deterministic π⋆ maximizing … simultaneously" | `∃ f : State → Action`, `detPolicy f = s ↦ δ_{f s}` | One f serves all states and all (s,a). It also serves V and Q together. The source's "resp." allows separate policies, so the Lean statement is at least as strong. True, so acceptable. |
| V⋆,σ := V^{π⋆,σ} = max_π V^{π,σ}; Q likewise | ∀ π s, V^{π,σ}(s) ≤ V^{detPolicy f,σ}(s), and the same for Q at every (s,a) | Because `detPolicy f` is itself a stationary policy, ≤-dominance is exactly "max is attained at π⋆", so both printed equalities hold. V⋆ and Q⋆ are definitional in the source. |
| Both balls | Two separate conjuncts, each with its own `∃ f` | Correct. The source treats TV and χ² as separate instances (`:52`). |
| RMDP data S, A finite, r ∈ [0,1], 0 < γ < 1 | `DiscountedMDP` (nonempty carriers, r ∈ [0,1], 0 ≤ γ < 1), universe-polymorphic `Type u`/`Type v` | γ = 0 is allowed, so the Lean statement is more general. Arbitrary Fintype carriers versus {1..S} make no difference. |

Not stated in the entry: history-dependent policies and dynamic adversaries. This is correct, since the printed claim
covers neither (CHECK fix 1/6). The docstrings make no dynamic-adversary claim.

## 2. Non-vacuity

- **Characterisation.** `robustPolicyQ_eq_reward_add_rowInf` proves Q^{π,σ}(s,a) = r(s,a) + γ·rowInf(U^σ(P⁰_{sa}), V^{π,σ})
  for every stationary π. This is `eq:bellman-equ-pi-infinite` (`:107`) exactly. The proof bounds the sInf from both
  sides: `csInf_le` at the worst-case kernel, and `le_csInf` with a nonempty set and the per-kernel bound
  `V^{π,σ} ≤ V^{π,K}`. Both `BddBelow` lemmas use the bound 0 from `trajectoryExpected{Q,Value}_bounds`. They are
  used correctly.
- **Nonemptiness.** Every `csInf_le` / `le_csInf` gets a witness `worstKernel U hU V`, which is admissible by
  `worstKernel_mem`. `hU` comes from `{tv,chi}Ball_family_rowAttains` at σ ≥ 0. Probe 2 independently shows that
  the nominal kernel is admissible for both balls at σ ≥ 0 (`nominal_admissible_tv`, `nominal_admissible_chi`).
- **Concrete probes, all compiled with the standard axioms only:**
  - `robustPolicyQ_discount_zero`: if γ = 0, then robustPolicyQ tvBall M σ π s a = r(s,a). So Q^{π,σ} is not constant
    whenever the reward varies, and no junk 0 can satisfy the entry.
  - `robustPolicyQ_tv_zero`: at σ = 0 (TV) the only admissible kernel is P⁰. Then robustPolicyQ = `M.trajectoryExpectedQ`
    of the nominal MDP. This ties the definition directly to the ordinary forced-first-action Q^{π,P⁰}.
- **Proof route re-checked.** For any π: Q^{π,σ} ≤ Q^{π,K⋆} = r + γ⟨K⋆_{sa}, V^{π,K⋆}⟩ ≤ r + γ⟨K⋆_{sa}, V⋆⟩ = robustQ V⋆.
  The middle step uses `optFix_super_worstKernel` and the policy-evaluation supersolution bound. On the other side,
  Q^{π⋆,σ} ≥ robustQ V⋆, because V^{π⋆,K} ≥ V^{π⋆,σ} = V⋆ and ⟨K_{sa}, V⋆⟩ ≥ rowInf. The inequality holds for every
  action a, not only greedy ones. The argument is sound, and I found no counterexample.

## 3. Axioms and tokens

The probe re-ran `#print axioms`. `Eq_mdp_value_Q_holds`, `exists_det_robust_value_Q_optimal_{tv,chi}`,
`robustPolicyQ_eq_reward_add_rowInf` and `robustPolicyQ_optPolicy` each depend only on
[propext, Classical.choice, Quot.sound]. This agrees with the builder's `axiom-probe.out`. A grep of the snapshot for
`sorry|admit|axiom |native_decide|implemented_by|extern|unsafe` found nothing.

## 4. Placement, names, docstrings

- `robustPolicyQ` is in namespace `StatisticalRL.RobustRL.Ch7`. Its module imports only `Ch7Definitions`, so it is a
  definitions-only module, and it is planned for `Formalization/RobustRL/Ch7/RobustQDefinitions.lean` [integrated instead in `Formalization/RobustRL/Ch7/Ch7Definitions.lean`; see the post-review note]. Good:
  `Statements/Ch7.lean` already imports `Ch7Definitions` and may import this module too.
- The proofs are in `StatisticalRL.RobustRL.DRVI`, planned for `DRVI/RobustQ.lean`. This matches `Optimality.lean`.
  No new name clashes with anything under `Formalization/`, checked by grep.
- `Eq_mdp_value_Q` is the label-derived name the CHECK recommends. Its docstring says "unnumbered display" and
  `robust_RL.tex:88–98`, and states that no numbered-ledger entry is added. No dynamic-adversary claim appears anywhere.

## R-items (must fix before integration)

None.

## F-items (disclosures / polish; non-blocking)

- **F1.** The `StatementProofs.lean` docstring says the printed σ > 0 "is weakened to the σ ≥ 0 the library needs".
  Suggested wording: "the library needs only σ ≥ 0 (it assumes less); the wrapper passes `hσ.le`". The current wording
  could be read as weakening the entry.
- **F2.** The `robustPolicyQ_eq_reward_add_rowInf` docstring cites `robust_RL.tex:103–117`. The display
  `eq:bellman-equ-pi-infinite` is at `:104–113` (line 107 is the equation, line 112 says "π stands for any policy").
  Tighten the citation. This theorem proves `eq:bellman-equ-pi-infinite` for stationary policies with the actual
  robust Q. The lead may want a separate displayed-claim index entry (for example `Eq_bellman_equ_pi_infinite`) and a
  COVERAGE note. That would be a separate change.
- **F3.** COVERAGE row 16 (Theorems 7.2/7.4) already says "existence of a deterministic optimal robust policy". Before
  this change that covered the value half only (CHECK Q3). After integration, point it at the new row, or say "value
  and Q".
- **F4.** Disclose that the Lean statement is stronger than the printed one in three ways, none of which is a source
  issue: (a) one f serves both V and Q, while the source says "resp."; (b) γ = 0 is allowed; (c) the library assumes
  only σ ≥ 0.
- **F5.** Disclose in COVERAGE that the statement is about the static adversary of `:76–84` and stationary randomized
  policies. History-dependent policies are not claimed (the optional strengthening has not been started).

## Recommended COVERAGE text

| Displayed claim `eq:mdp-value-Q`, robust chapter lines 88–98 (robust V and Q defined at 71–84; policies prelim.tex:66) | [Ch7/Ch7Definitions.lean](../Formalization/RobustRL/Ch7/Ch7Definitions.lean) (`robustPolicyQ`; originally proposed as `Ch7/RobustQDefinitions.lean`), [DRVI/RobustQ.lean](../Formalization/RobustRL/DRVI/RobustQ.lean), [Ch7.lean](../Formalization/Statements/Ch7.lean) (`Eq_mdp_value_Q`), [Ch7Proofs.lean](../Formalization/Statements/Ch7Proofs.lean) | **Printed claim proved** for both the TV and the support-aware χ² uncertainty sets, for every σ > 0 (the library needs only σ ≥ 0). One deterministic stationary policy maximizes the robust value at every state and the robust Q-function (inf over admissible kernels of the actual forced-first-action Q) at every state-action pair, over all stationary randomized policies. The maxima are attained, so V^{⋆,σ} = V^{π⋆,σ} = max_π V^{π,σ}, and the same holds for Q. The adversary is static, as in the book: one (s,a)-rectangular kernel for the whole trajectory. The library also proves robust Bellman consistency for Q^{π,σ} (`robustPolicyQ_eq_reward_add_rowInf`). History-dependent policies are not claimed. This is a displayed claim, so it adds no numbered-ledger entry. Independently source-reviewed ([critic](critic-robust-q.md)). |
