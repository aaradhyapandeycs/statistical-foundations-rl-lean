# CRITIC: Thm3_9_positiveN (Theorem 3.9, any empirically optimal deterministic policy)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this critic reviewed the pre-integration snapshot; integrated into the library on 2026-11-08 (imports-only changes plus the F2/F3 docstring fixes). Snapshot files map to the intended integrated locations as follows: `WorstTie.lean` → `Formalization/Generative/FiniteHorizonWorstTiePlanner.lean`; `SelectorPipeline.lean` → `Formalization/Generative/FiniteHorizonSelectorPipeline.lean`; `AnyTie.lean` → `Formalization/Generative/FiniteHorizonAnyTieSample.lean`; `Statement.lean` → the `Thm3_9_positiveN` entry in `Formalization/Statements/Ch3.lean`; `StatementProof.lean` → the `Thm3_9_positiveN_holds` wrapper in `Formalization/Statements/Ch3Proofs.lean`. Short file names below refer to the reviewed snapshot files, and the file hashes are those of the snapshot. The review text below is otherwise unchanged.

Critic: independent (did not build). Date 2026-11-08. Builder files untouched; probes only in the
reviewer's private probe folder and oleans only in the reviewer's private olean folder.

## Verdict: ACCEPT WITH DISCLOSURES

The disclosures are the ones the drafts already carry: `N > 0` (scope stays "restricted"), and the
policy class is deterministic Markov policies (the monograph's convention, prelim.tex:738–739).
No R-item. F-items below are integration and wording fixes for the lead.

## Target identity

The builder's reviewed snapshot (5 files) verified with `shasum -a 256 -c`
against the builder's snapshot hash list (all OK). The builder's live working files are byte-identical to it (`cmp`).

```
d54d0df1a45e1d58ac1972a6e98b5c720c51f8ea11218b23c14bcc20b464401d  AnyTie.lean
9ccadec2a59255e49e06e3b763d0a6b4098e4551ed2d61137083ac6763d8e8d6  SelectorPipeline.lean
2634626ccae3a528584c09fcf06b51a4ddb5f1872deb4139d25e7196b0f63d03  Statement.lean
39c9e56f03cb2d6eac83ff0ca1d6b03069e37378501c0997e9d2cbb9a152561a  StatementProof.lean
8b28d82ed0938f4245c7e534dafd4f17c4c197a70af36b30bab75c6871885c9f  WorstTie.lean
```

## Source read first

- MB:2524–2546: step 1 draws N i.i.d. samples per (s,a,h), P̂_h = empirical frequencies; step 2
  "Compute an optimal policy π̂⋆ for the empirical MDP M̂ = (S,A,P̂,r,H)" (true rewards kept).
- MB:2547–2549: backward-induction remark (decoupling via causality); no tie rule fixed.
- MB:2551–2570: ∃ universal c₀>0; ∀ δ>0, 0<ε≤H; w.p. ≥ 1−δ, ∀(s,h) V_h^{π̂⋆} ≥ V_h⋆ − ε and
  ∀(s,a,h) Q_h^{π̂⋆} ≥ Q_h⋆ − ε, provided N ≥ c₀H³log(HSA/δ)/ε².
- prelim.tex:738–739: an optimal deterministic policy maximizes V and Q simultaneously for all
  (s,a,h); π⋆ denotes such a policy throughout.

## Checks

### (1) Prop fidelity — PASS
- `∃ c₀, 0 < c₀ ∧ ∀ State Action ...`: c₀ precedes all carriers, models, H, N, δ, ε. (Universe
  parameters of the def precede c₀, as in every existing Ch3 entry; the proof uses 8640 uniformly.)
- `0 < δ`, `0 < ε`, `ε ≤ H`; threshold `c₀·H³·log(H·|S|·|A|/δ)/ε² ≤ N` — matches (EqnSamples-finite).
- `hN : 0 < N` explicit — disclosed. Builder's "no content lost" argument checked: N = 0 forces
  log(HSA/δ) ≤ 0, so δ ≥ HSA ≥ 1 (H ≥ 1 from 0<ε≤H, S and A nonempty from `EnvironmentStage`),
  where 1−δ ≤ 0 makes the claim trivial. Correct.
- Event: ∀ f : ℕ → State → Action, (∀ h<H, ∀ s, V̂^f_h(s) = V̂⋆_h(s)) → ∀ h<H, (∀ s, V⋆_h − V^f_h ≤ ε)
  ∧ (∀ s a, Q⋆_h − Q^f_h ≤ ε). Stage indexing: `controlled` applies `π k` at list position k and
  `policyTrajectorySuffix es f h = trajectoryValue ((controlled es f).drop h)`, so `f h` acts at
  stage h. Empirical stages keep the true reward (`empiricalStage.reward := (E h).reward`).
- Reading of "an optimal policy of M̂": V-optimality at every stage and state is equivalent to the
  prelim notion (simultaneous V and Q optimality at all (s,a,h)), since Q^f_h = r + P̂ V^f_{h+1}
  and Q at the last stage is r. The weaker "optimal from stage 1 only" reading makes the printed
  claim false (counterexample in `critic-small-batch-2-plan-check.md` (a), which I re-derived: an
  unreachable stage-2 state with a reward-0/reward-1 action pair). The chosen reading is right.
- Non-vacuity — PROBED: `critic_exists_empirically_optimal` (for every data set the backward-greedy
  output satisfies the hypothesis) and `critic_new_implies_causal` (`Thm3_9_positiveN →
  Thm3_9_causal_positiveN`, same c₀) both compile. So the new entry is strictly at least the old
  one and the hypothesis is never empty.
- Measurability — PROBED: `critic_all_measurable` shows every subset of `Samples` is measurable
  (finite sample space, ⊤ on State), so `.real` of the ∀f-event is a genuine probability, not an
  outer-measure artifact.
- No fallback binder, no `hH` in the Prop. Prop body is token-identical (whitespace-normalized) to
  the batch plan's (a) draft.

### (2) Worst-tie reduction — PASS
- W1 `worstActions_drop`: planner at index h+k = planner on `es.drop h, fs.drop h` at k. With W4
  `worstTieSelector_factorsFuture`, decisions at stages ≥ h+1 are unchanged when all samples at
  stages ≤ h are overwritten (`completeFutureData h N x (futureData h N data)`); the true stages
  are data-free. This is exactly the shape `futureValue_row_bernstein` consumes.
- W2 `worstActions_suffixOptimal` → `SelectorEmpiricallyOptimal` for every data, h, s.
- W3 `worstActions_dominated_suffix`: for every g that is `SuffixOptimal` on the empirical stages,
  V^w_h(s) ≤ V^g_h(s) at every h and s (true model). Proof checked by hand: suffix optimality at 0
  and the tail gives g₀(s) ∈ Â(s); then induction + monotonicity of expectation + minimality of w.
- `suffixOptimal_of_forall_fin` converts the Prop's `∀ h : Fin H` to all n (both sides 0 beyond H).
- Q bound from V bounds at every h via `policyTrajectoryQSuffix_loss_le_of_values`.
- Selector pipeline hypotheses (`hsel`, `hopt`) are discharged in `mainSample_anyEmpiricalOptimalPolicy`
  by W4/W2; the export `exists_universal_anyEmpiricalOptimalPolicy_sample_constant` has exactly the
  Prop's type and no extra hypotheses. The worst-tie planner reads E — an analysis device only;
  the docstring says so.

### (3) Constant / branches — PASS
- 8640 unchanged (same as `FiniteHorizonMainSample.lean`). δ ≥ 1 branch trivial. H = 1 branch:
  pathwise zero loss via `oneStage_policyTrajectorySuffix_eq` (any f). H = 0 excluded by 0<ε≤H.

### (4) Axioms / tokens — PASS
- Independent recompilation of all five snapshot files (copies with the module prefix changed in imports only,
  builder's working prefix → reviewer's private prefix, bodies identical) via `bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean`:
  all exit 0, no errors.
- `Probe.lean` in the reviewer's private probe folder (exit 0): `Thm3_9_positiveN_holds`, the export,
  `worstActions_dominated_suffix`, `worstTieSelector_factorsFuture`, `mainSample_selectorPolicy`,
  and `critic_new_implies_causal` depend only on [propext, Classical.choice, Quot.sound].
- grep for sorry/admit/axiom/native_decide/implemented_by/extern/unsafe/opaque/maxHeartbeats: none.
- No new declaration name clashes with `Formalization/`.

### (5) Ledger drafts — PASS with fixes
The json draft repoints `lean_export`, `lean_statement`, `lean_statement_proof`, `evidence`, and keeps
`statement_scope` "restricted (N>0 only) ...", which satisfies F-a1. The causal entry is retained and
named in COVERAGE and SOURCE-ISSUES (F-a2). Proof-route note is in the docstring (F-a3).

## R-items (blocking)
None.

## F-items (non-blocking, lead to apply at integration)
- F1. `evidence`/COVERAGE link: the drafts point at `docs/critic-thm3-9-any-tie.md`; publish this
  report there (minus local paths) or repoint. Drop "(pending)" from the COVERAGE link text.
- F2. Make the F-a2 docstring addition to `Thm3_9_causal_positiveN` non-optional (the CHECK says
  "should"): name `Thm3_9_positiveN` as the general result.
- F3. Docstring nit in `Thm3_9_positiveN` and SOURCE-ISSUES draft: "(or an empty carrier)" cannot
  occur (H ≥ 1 and `EnvironmentStage` gives nonempty State and Action). Harmless; may delete.
- F4. Disclosure wording: keep the word "deterministic" in `statement_scope` and COVERAGE (it is
  there). Randomized empirically optimal policies are not covered; this matches prelim.tex:739's
  convention and is not a source-fidelity finding, but must not be dropped.
- F5. Maintainability: `SelectorPipeline.lean` duplicates the existing all-level Bernstein pipeline.
  Optional later refactor: derive the causal export from the selector pipeline.

## Ledger text (for the critic-evidence entry)
Theorem 3.9 (`Thm:sample-compl-finite`, MB:2551–2570): `Thm3_9_positiveN` independently reviewed
— ACCEPT WITH DISCLOSURES (N > 0; deterministic policies per prelim.tex:738–739). Covers every
policy optimal for the empirical MDP at every stage and state, quantified inside the event; proof by
domination of a causal worst-tie analysis planner; constant 8640; axioms propext, Classical.choice,
Quot.sound. `Thm3_9_causal_positiveN` retained as the backward-greedy special case (implied by the
new entry, probed).

## Commands run
- `shasum -a 256 -c` against the builder's snapshot hash list (OK ×5); `cmp` live vs snapshot (same ×5).
- `bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean <reviewer probe folder>/<X>.lean` for X in Statement, WorstTie, SelectorPipeline, AnyTie, StatementProof — all exit 0 (2–4 s each).
- `bash scripts/lean-local.sh <reviewer probe folder>/Probe.lean` — exit 0, 11 s; output in `Probe.out`.
