# CRITIC: `Thm3_9_minimaxLowerBound` (finite-horizon generative minimax lower bound)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this critic reviewed the pre-integration snapshot; integrated into the library on 2026-11-08 (imports-only changes, one import rerouted through FiniteHorizonPolicyEvaluationConsumption for the frozen import-layering gate, plus the R1/R2/R4 docstring disclosures). Snapshot module names map to the intended integrated modules as follows: `AssouadWeighted` → `Formalization/Probability/Fano/AssouadWeighted.lean`; `SamplingAtoms` → `Formalization/Generative/FiniteHorizonSamplingAtoms.lean`; `Family` → `Formalization/Generative/FiniteHorizonLowerBoundFamily.lean`; `FamilyBounds` → `Formalization/Generative/FiniteHorizonLowerBoundBounds.lean`; `Main` → `Formalization/Generative/FiniteHorizonLowerBoundTheorem.lean`; `Statement` → the `Thm3_9_minimaxLowerBound` entry in `Formalization/Statements/Ch3.lean`; `Proofs` → the `Thm3_9_minimaxLowerBound_holds` wrapper in `Formalization/Statements/Ch3Proofs.lean`. Short module names below refer to the reviewed snapshot files, and the file hashes are those of the snapshot. `TRIAGE` refers to the lead's private work list, which is not published. The review text below is otherwise unchanged.

Independent critic; did not build. Nothing under `Formalization/`, `Formalization.lean`, the builder's
working tree or the project's `Formalization*` build outputs was edited. Probes: kept in the reviewer's private probe folder.

## Verdict: ACCEPT WITH DISCLOSURES

The statement is a faithful formal reading of the prose claim MB:2585 under the book's protocol; the
proof compiles from the reviewed snapshot with the standard axioms only. Remaining items are
disclosures, not defects. None blocks integration.

## Target identity

The builder's snapshot hash list re-verified: all seven reviewed snapshot files match, and the builder's live
working files are byte-identical (`cmp`) to the snapshot.

    5ef39d463cef3e93be059c3595c38b163a9ac7ee4d4cf57171ba94e172a8c7c9  AssouadWeighted.lean
    88a7719912545ba7e1aab8ebab5177228137a4bb34af142e6e5e7786283adb7f  Family.lean
    7d86415c4ddd18eab3b53909855bfa776b248da1e80d8fd4d46a7eb10044eca9  FamilyBounds.lean
    e6c67034d6331a33771eccd7afb6c1c443b5c6d82d519de28b0533f0ababdcd5  Main.lean
    59fb0a3697254ff41d116102e4052ca6fcaf79863dc5191a74b94ef251fbcc65  Proofs.lean
    21de4d20a5ed38d639d72694cf0282b1ea18d6b90fc1cc1a960c3fff53b9d2c8  SamplingAtoms.lean
    520d1d719f0b2d22c0b8c6d952a185448c5b119fc42a99647fe65895acab1c8e  Statement.lean

## Source read first

MB = `source/upstream/tex/chapters/generative_model_model_based.tex`. Protocol :19–30: independent
draws `s(s,a,h) ~ P_h(·|s,a)` per query, rewards fully known (:30). Theorem 3.9 :2551–2570: per-tuple
`N ≥ c₀H³log(HSA/δ)/ε²`, guarantee V and Q at every (s,h), range `0<ε≤H`. Prose :2573–2585: total
`Õ(SAH⁴/ε²)` (eq :2580–2583) "provably minimax optimal" citing `domingues2021episodic`. No printed
lower-bound theorem, no constants, no domain.

## (1) Statement fidelity

- Quantifier order: `∃ c c₁, 0<c ∧ 0<c₁ ∧ ∀ S A H N ε …` — constants universal over all instances,
  estimator, and E chosen after the estimator. Correct minimax order. (Probe confirms the
  existentials are outermost.)
- Domain: `2≤S, 2≤A, 2≤H, 0<ε≤c₁H`. Each exclusion is necessary (H=1 or S=1 or A=1: known rewards
  determine an optimal policy with zero samples; ε≥H: V∈[0,H] so the event `ε < gap` is empty).
  The gap `c₁H < ε ≤ H` is not covered; acceptable because c₁ is existential and the prose has no
  range ((0,H] at :2578 belongs to the upper bound). Disclosed.
- Budget: `N ≤ c·H³/ε²` per (s,a,h) with c = 2⁻²⁸; the total is `HSA·N`. This is the book's
  per-tuple reading of :2573–2583. The S·A factor is inherited from the uniform protocol, not tested
  (only copy 0, states 0 and ⌊S/2⌋, actions {0,1} carry information). Disclosed.
- `samplingLaw E N` = `Measure.pi` over `(Fin H × S × A) × Fin N` of the row measures
  `(E h).transition s a` — exactly N independent next-state draws per (s,a,h), non-adaptive. Matches
  :25–28. Rewards are passed to the estimator as the table `fun h s a ↦ (E h).reward s a`; in the
  hard family the table is σ-independent (`hardStages_reward`, `rfl`), so it leaks nothing. Matches :30.
- Estimator class: `Seed : Type` with any `MeasurableSpace` and probability measure ν, seed
  independent of the data (product measure), `piHat : Seed → rewards → samples → ℕ → Fin S → Fin A`.
  Deterministic estimators are `Seed = Unit`; the probe instantiates the library theorem with
  `Measure.dirac ()` and an arbitrary `alg`, the measurability side condition being automatic.
  The estimator may depend on S, A, H, N, ε (bound before it). Instance check: the wrapper only
  typechecks because the seed σ-algebra in `hmeas` is the binder instance (not the file-wide
  `statementStateMeasurable := ⊤`), so the measurability hypothesis is not trivialized.
- Output: a deterministic nonstationary policy per seed (steps ≥ H are ignored,
  `policyTrajectorySuffix_congr`). Matches the book's output `π̂⋆`.
- Failure event: `∃ s, ε < V⋆₁(s) − V^{π̂}₁(s)` (stage index 0), i.e. negation of Theorem 3.9's
  V-clause at h=1; stronger than negating the full V∧Q guarantee. Probability `≥ 1/8` under
  `(samplingLaw E N).prod ν`. Correct.

## (2) Junk values / measurability

- `optimalValue (List.ofFn E)` and `policyTrajectorySuffix (List.ofFn E) f 0` are the library's
  backward-induction value and actual trajectory value on the full H-stage list; no `drop` beyond
  length, no default branch reached (`List.ofFn` has length H, policy steps < H used).
- `.real` of the event: the event is proved measurable (`measurableSet_policy_event` +
  `measurableSet_of_sections`, used inside `samplingLaw_prod_real`), so `.real` is the genuine
  probability, not an outer-measure value. This is exactly why the measurability hypothesis exists.

## (3) Math spot-checks (deviations 1–3)

- ε₀ = 2048ε ≤ 2048·H/4096 = H/2: admissible for `onlineLBStages` (`hεH : ε₀ ≤ H/2`).
- K = Nε₀²/H³ ≤ 2048²·2⁻²⁸ = 2²²/2²⁸ = 1/64. ✓
- Bhattacharyya (dev. 1): product over atoms factorizes (`sum_sqrt_samplingAtom`); only the N copies
  of row (h,0,1) differ (`hardStages_prob_eq_of_ne`); each has BC ≥ 1 − u²(H+1)/2 with u = ε₀/H²
  (`flipped_row_ge`, Bernoulli rows 1/H vs 1/H − ε₀/H²); so BC ≥ 1 − Nu²H = 1 − K. Le Cam:
  test-error sum ≥ BC²/2 (`bhattacharyya_sq_le_test_error`; standard since 1−TV ≥ 1−√(1−BC²) ≥ BC²/2).
  θ = (1−K)²/2 ≥ (63/64)²/2 ≈ 0.4845. ✓
- Weights w_h = ε₀(H−h−1)/(16H²): Σ = ε₀(H−1)/(32H) ≥ ε₀/64 for H ≥ 2. ✓
- Reverse Markov (dev. 2), t = 1/10, Z ∈ [0,W]: Σ_σ Q_σ(ω) ≥ 2^H/8 needs
  t + (1−t)/8 = 0.2125 ≤ θ/2 ≈ 0.2423 (`constant_check`). Applied per seed ω to linear σ-sums, then
  integrated over ν; no σ is chosen before integrating — sound. Then some σ has probability ≥ 1/8
  (averaging, by contradiction). ✓
- Gap: on Z ≥ tW, gap at state 0 ≥ W/10 ≥ ε₀/640 = 3.2ε > ε via the library
  `onlineLBStages_value_gap` (Lemma 5.20 machinery, `ValueGap.lean:414`). ✓
- All of the above is Lean-checked; arithmetic re-derived independently and agrees.

## (4) Axioms and tokens

- Re-probe `CriticProbe.lean` in the reviewer's private probe folder (output `CriticProbe.out`): `Thm3_9_minimaxLowerBound_holds`,
  `minimaxLowerBound`, `gap_ge_weighted_loss`, `bhattacharyya_flip_ge`,
  `bhattacharyya_sq_le_test_error` all depend only on `[propext, Classical.choice, Quot.sound]`.
- Snapshot `Main.lean` and `Proofs.lean` recompiled from the snapshot to the reviewer's
  private olean folder (exit 0; log kept in the reviewer's private probe folder).
- Grep for `sorry|admit|axiom|implemented_by|extern|unsafe|native_decide|opaque|maxHeartbeats 0`
  over the snapshot: no hits.

## (5) Docstring disclosures (F1–F4)

- F1: unsuffixed name justified — randomized estimators are covered. Docstring discloses (a) uniform
  per-tuple non-adaptive protocol, S·A inherited; (b) copy 0 / actions {0,1}; (c) existential c₁
  (witnesses c = 2⁻²⁸, c₁ = 1/4096); (d) seeded estimators with known rewards. SATISFIED.
- F2: averaged weighted Assouad as finite sums over atoms; seed handled pointwise + integration.
  SATISFIED.
- F3: domain recorded as a scope disclosure (drafted in the builder's status file), no numbered Candidate, "No source
  error". SATISFIED in draft; lead must land it.
- F4: docstring states the cited `domingues2021episodic` theorem (total/adaptive budget) is NOT
  established. COVERAGE text drafted. TRIAGE locator :2589 → :2585 still to be applied by the lead.
  OPEN (lead action only).

## R-items (disclosures; none blocking)

- R1 (measurability, real but negligible narrowing). The hypothesis requires seed-measurable outputs
  for every reward table r, though the proof uses only the hard family's table r₀. Because E is
  existential, a user cannot remove this by modifying a non-measurable estimator off r₀ (r₀ is
  internal to the proof). It excludes only estimators with non-measurable seed dependence, and it is
  what makes the event measurable. Disclosed in the docstring; ask that the COVERAGE/scope line also
  say "output actions measurable in the seed".
- R2 (policy class). Outputs are deterministic policies per seed. An estimator emitting a Markov
  stochastic policy, judged by V of that stochastic policy, is not literally covered (the proof's
  expectation-based bounds would extend, but this is not claimed). Matches the book's deterministic
  `π̂⋆`; add "deterministic (seed-randomized) policy output" to the scope line.
- R3 (Seed universe 0). Disclosed in the docstring; harmless.
- R4 (no log factor). The bound matches `H³/ε²` per tuple without the `log(HSA/δ)` of Thm 3.9, and a
  fixed failure probability 1/8 (not δ-dependent). Consistent with the prose `Õ`; no claim of a
  δ-dependent lower bound should be made.
- R5 (constant magnitude). With ε ≤ H/4096, the admitted budget satisfies cH³/ε² ≥ H/16, so N ≥ 1 is
  in scope only when ε is small relative to H; this is the usual asymptotic minimax meaning and c is
  existential. No action.

## Proposed ledger text

COVERAGE row (MB:2573–2585): "Prose minimax-optimality claim (MB:2585): formal reading of prose in
the book's per-tuple protocol — `Thm3_9_minimaxLowerBound`: for S, A, H ≥ 2 and 0 < ε ≤ c₁H, any
seed-randomized estimator (output actions measurable in the seed, deterministic nonstationary policy
output) with N ≤ c·H³/ε² independent samples per (s,a,h) fails stage-1 ε-optimality with
probability ≥ 1/8 on some instance (c = 2⁻²⁸, c₁ = 1/4096). Does not establish the cited
domingues2021episodic total-budget/adaptive theorem."

SOURCE-ISSUES scope line ("Statement-index scope disclosures", not a Candidate): "`Thm3_9_minimaxLowerBound`
(formal reading of the prose minimax claim MB:2585): domain S, A, H ≥ 2 and 0 < ε ≤ c₁H with
existential c₁ (witness 1/4096); each exclusion is necessary. Uniform per-(s,a,h) protocol, so the
S·A factor is inherited, not tested (copy 0, actions {0,1} only). Estimators: seed on an arbitrary
probability space (universe 0), output actions measurable in the seed for every reward table,
deterministic nonstationary policy per seed. Failure probability 1/8, no log factor. No source error."

## Critic artifacts (sha256)

Hashes of this report and the probes were given in the critic's private report message and are not reproduced here.
