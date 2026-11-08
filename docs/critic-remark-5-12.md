# CRITIC: Remark 5.12 (Gaussian-bandit minimax lower bound; UCB optimality)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this review covered the builder's pre-integration snapshot. To respect the frozen import-layering gate (no new import edge from `Formalization/Statements/Ch5.lean`), the definitions of Defs (`history`, `armAt`, `regret`, `hardMean`) were not integrated as a separate definitions module: they were appended verbatim to the existing definitions module `Formalization/Online/Bandit/UCBDefinitions.lean`, which the statement file already imports. The proof modules were integrated unchanged except for their imports, as `Formalization/Online/LowerBound/GaussianBanditMeasurability.lean` (Measurability), `Formalization/Online/LowerBound/GaussianBanditShift.lean` (GaussianShift), `Formalization/Online/LowerBound/GaussianBanditChangeOfMeasure.lean` (ChangeOfMeasure), `Formalization/Online/LowerBound/GaussianBanditKL.lean` (KL), `Formalization/Online/LowerBound/GaussianBanditMinimax.lean` (Minimax) and `Formalization/Online/LowerBound/GaussianBanditUCBOptimal.lean` (UCBOptimal). The statement files became the entries `Remark5_12_lowerBound` and `Remark5_12_restricted` in `Formalization/Statements/Ch5.lean`, with their proofs in `Formalization/Statements/Ch5Proofs.lean`; on integration the entry docstrings were changed to address F-b and F-c. Short names of the proof modules below refer to these integrated files (Defs, Statements and StatementsProofs name the reviewed snapshot files); the file hashes quoted below are those of the reviewed snapshot. The review text below is otherwise unchanged.

Date: 2026-11-08. Independent critic; did not build. No builder file, nothing under `Formalization/`
and no `Formalization*` olean was touched. No paper fetched. No lake / lean-lsp used.

## Inputs and hashes

- Source read first: `onlineRL.tex:2675–2732` (bandit detour, Lemma 5.21 `lem:online-lb-testing`
  :2709–2721, the remark :2725–2729), `bandits.tex:10–75` (setting :15–48, regret :66–70),
  `bandits.tex:285–300` (minimax-optimal up to logs, :296).
- The builder's reviewed snapshot (9 files) verified against the builder's snapshot hash list
  (all 9 match); the builder's live working files are byte-identical (`cmp`).
  - Statements.lean `cf7efc08860d9ffad3a5ee5b38fd09aced2cd457925943040b46190fb83f770a`
  - StatementsProofs.lean `a2115cc45734b00f75a47198cc7de52e88874169d33d44b0cf48ef81f442ce35`
  - Defs.lean `12d7c7f230d92392ffdbb71faafaa8a5fd45b9af5c0e04abcf429a3a764bde76`
  - Minimax.lean `4001d133aeec5fdf065ee8143ed41c1d361db0fe8fc8406b1e1fb934626a992a`
  - KL.lean `41b1f4404ed7ab1f2b20d95a35a66254a93e156f6a9df0dd442afce2ab77f5c6`
  - ChangeOfMeasure.lean `280af60b5444255df80696acada3cc6ca1fc0b725e76e802b72fbb4fed271f68`
  - GaussianShift.lean `72bdfe79eaa581561a938200898db5d34565967051358c7609e82b0f7f8add4f`
  - Measurability.lean `e84f2b2d084c29e19fa1b10367eb1c37b7c308f65a49812408c6241d97e55795`
  - UCBOptimal.lean `2b98c300823a3af9466b8e8c36a2927f752223ae5ad9c3a78ede90492e80ae4b`
- Critic probe: `Probe.lean` in the reviewer's private probe folder
  (sha256 `e64018e23944799e99a8abb1e016d6400487b87615b635e0823de760fa2c8696`), output
  `probe.out` in the same folder. Command (foreground, once after a one-line fix):
  `bash scripts/lean-local.sh <reviewer probe folder>/Probe.lean` → EXIT 0,
  0 errors, ~14 s. It imports the builder's existing working oleans (built from the identical files).

## Verdicts

| Entry | Verdict |
|---|---|
| `Remark5_12_lowerBound` | **ACCEPT WITH DISCLOSURES** (D1–D3) |
| `Remark5_12_restricted` | **ACCEPT WITH DISCLOSURES** (D1–D5; `_restricted` suffix is correct) |

No refutation found. No R-item blocks integration.

## 1. Fidelity of `Remark5_12_lowerBound`

- **Quantifier order.** `∀ A T, 2 ≤ A → A ≤ T → ∃ μ (family of A vectors), μ ∈ [0,1] ∧ ∀ Seed ν arm,
  measurable → ∃ i, Integrable ∧ (1/16)√(AT) ≤ E regret`. The family is fixed before the learner:
  this is inf_learner max_i, the stronger (fixed-family) form, implying the ∀L ∃μ form. The learner
  may "know" the family but not `i` — the standard minimax set-up. Correct.
- **Means in [0,1].** `hardMean ε` with ε = ½√(A/T) ≤ ½ takes values {0, ε/2, ε} ⊂ [0, ½];
  `hardMean_mem_Icc` proves it. Probe P7 confirms the family values.
- **Learner class.** `arm t : Seed → (Fin t → Fin A × ℝ) → Fin A`, seed from an arbitrary
  `(Seed : Type, ν)` probability space, product with the noise (independent). `history` (Defs.lean)
  is defined by recursion: row `t` appends `(a_t, μ a_t + ζ t a_t)` with `a_t = arm t σ (history t)`.
  The arm map never receives `ζ`, μ, or any unpulled reward — only the seed and past (arm, observed
  reward) pairs. Probes: P4 (`armAt t` depends only on noise rows `s < t`, via `history_congr`),
  P5 (the last history entry is exactly the pulled arm and its noisy reward). No peeking at the
  noise table or the future is possible. Matches bandit feedback `bandits.tex:47–48` and the
  "selects an arm based only on the observations collected prior to round t" of OL:2705.
- **Noise model.** `gaussianNoiseTable T A = Measure.pi (fun _ => Measure.pi (fun _ => N(0,1)))`
  (probe P6, `rfl`): iid N(0,1) over (round, arm), exactly `bandits.tex:37–42`. `extendNoise`
  pads with zeros after the horizon; rounds `< T` only read rows `< T` (P4), so the law of
  everything the regret depends on is unchanged.
- **Regret.** `regret = T·(⨆ a, μ a) − Σ_{s<T} μ(a_s)` = `bandits.tex:66–70` pseudo-regret
  (r⋆ = max is the `iSup` over the finite nonempty `Fin A`); the entry integrates it over
  `ν ⊗ table`, i.e. `E[Regret(T)]` as used at `:296`. Non-vacuity probes: P1 instantiates the
  statement for the constant learner "always arm 0" (Seed = Unit, ν = dirac); P2 shows the oracle
  constant learner has regret exactly 0 on a fixed μ (so the regret is not junk-large and the ∃-family
  is essential); P3 gives regret = T(r⋆ − μ a) for constant learners. A wrongly defined regret
  would show up here; none does.
- **Constant and range.** `(1/16)√(A·T)` with `2 ≤ A ≤ T` (Theorem 5.1's range). Remark gives no
  constant; disclosed as ours. Arithmetic checked: ε = ½√(A/T), B = ε²T/2 = A/8, Fano ≥ 1/4,
  regret ≥ (ε/2)(T/4) = εT/8 = √(AT)/16.
- **Integrable conjunct** present (F4); proved by `integrable_regret` (bounded + measurable).

## 2. `Remark5_12_restricted`

- Shares the lower-bound conjuncts verbatim, then: `∀ r ∈ [0,1]^A`, UCB regret integrable and
  `E[UCB regret on r] ≤ 128·√L · E_{μ i}[regret of arm]`, with `L = log(T²/δ)`, `0 < δ < 1`, same
  `ucbAction tie L r` and the same tie hypothesis `∀ t s, s.Nonempty → tie t s ∈ s` as
  `Thm5_1_restricted` (Ch5.lean:1039–1050, compared token by token). It therefore inherits exactly
  that tie-rule restriction.
- **What is compared to what.** The right side is one arbitrary learner's regret on its own hard
  member `i`; since the statement holds for every learner, it gives
  sup_{r∈[0,1]^A} E[UCB regret] ≤ 128√L · inf_learner max_i E_i[regret] ≤ 128√L · minimax value
  over [0,1]^A (hard family ⊂ [0,1]^A). This is the "minimax-optimal up to log factors" notion of
  `bandits.tex:296`. Meaningful, not vacuous (the right side is ≥ (1/16)√(AT) > 0).
- **Factor.** 8√(ATL) = 128√L·(1/16)√(AT); L ≥ log 4 > 0 since T ≥ 2, δ < 1 (`hL`). Correct.
- The UCB comparator is via the existing library `ucb_regret_bounds`, not re-proved.

## 3. Math spot checks

- **`lintegral_history_shift_joint` (general shift c).** States
  ∫ g(σ, H_T^{μ+c}) d(ν⊗P) = ∫ g(σ, H_T^{μ}) · exp(Σ_s c(a_s) z_{s,a_s} − c(a_s)²/2) d(ν⊗P),
  arms a_s under μ. Correct for arbitrary c: at round s only the pulled coordinate's law is tilted
  N(0,1) → N(c(a_s),1), and μ(a)+N(c(a),1) = (μ+c)(a)+N(0,1); a_s is predictable. Proof by induction
  on T with last-row split + 1-D shift `lintegral_gaussian_shift` (verified: Gaussian pdf ratio
  e^{cy−c²/2}). Taking g = 1 gives total mass 1.
- **`klDiv_tiltQ`.** KL(P ‖ P·e^f) = ofReal(E_P Σ_s c(a_s)²/2). Correct: −E f, with the predictable
  zero-mean term killed (`integral_predictable_coord`, row-s split). Direction KL(P₀‖P_j) matches
  `reverseFano_test_error_lower`'s `hKL` (ReverseTest.lean:84). Uses F2 route (`klDiv_of_ac_of_integrable`).
- **Per-round reverse Fano, B = A/8.** Σ_{j≥1} c_j(a)²/2 ≤ ε²/2 per round (only arm j differs, at
  most one j per pulled arm), so Σ_j KL ≤ ε²T/2 = (M+1)/8 = A/8; `fano_quarter` gives 1/4. The test
  ψ_s = a_s under instance 0; `tiltQ_arm_ne` transfers Q_j(ψ_s ≠ j) to P(a_s^{(j)} ≠ j) (requires
  only the first s history entries, `history_restrict`). Correct.
- **`extendNoise` device** does not change the law: histories at rounds ≤ T read only rows < T,
  which are the table's own coordinates (`extendNoise_snoc_of_lt`, `armAt_snoc_of_le`, P4).

## 4. Axioms, tokens, F5

- Re-probed (probe.out): `Remark5_12_lowerBound_holds`, `Remark5_12_restricted_holds`,
  `minimax_lower_bound`, `ucb_minimax_optimal`, `lintegral_history_shift_joint`, `klDiv_tiltQ`,
  `tiltQ_arm_ne`, `lintegral_gaussian_shift`, `integral_predictable_coord` — all exactly
  `[propext, Classical.choice, Quot.sound]`.
- Forbidden-token grep (sorry, admit, axiom, native_decide, implemented_by, extern, unsafe, opaque,
  set_option, private, macro, elab): no hits in any snapshot file.
- **F5:** Defs.lean imports only `Formalization.Online.Bandit.UCBDefinitions` and contains only
  `def`s (`history`, `armAt`, `regret`, `hardMean`); Statements.lean imports only Defs and has no
  proofs. Wrappers just apply `minimax_lower_bound` / `ucb_minimax_optimal` (no restatement).
- F1 (two entries, `_restricted` on UCB part), F2 (KL route), F3 (row-split zero mean, no
  `iIndepFun_pi`), F4 (Integrable + fixed-family form, docstring says so) — all satisfied.

## Items

R-items (blocking): none.

F-items (non-blocking, for lead at integration):
- **F-a.** On move to `Formalization/Online/LowerBound/…` and `Statements/Ch5.lean`, re-check the
  Ch5 entries are byte-identical to the snapshot `Statements.lean` bodies (namespaces only change),
  and re-run the axiom audit through `Formalization.lean`.
- **F-b.** `Seed : Type` (universe 0) in the Prop; adequate (any probability space used in practice,
  e.g. `ℕ → unitInterval`), but mention it in the docstring/disclosure line.
- **F-c.** Docstring of `Remark5_12_restricted` could add that the comparison holds for every learner,
  hence against the minimax value over [0,1]^A (the reading-aid point of §2).

Disclosures:
- **D1.** Formal reading of an informal remark; constant 1/16 and range 2 ≤ A ≤ T are ours (match
  Theorem 5.1's range); the remark's "proof argument can be adapted" is realized by per-round reverse
  Fano with the Gaussian KL, the conclusion (Ω(√(AT)) minimax bound) is what is indexed.
- **D2.** Learner class: arm maps jointly measurable in (seed, history); seed space `Seed : Type`.
- **D3.** Regret is the expected pseudo-regret (`bandits.tex:66–70`, as at `:296`); hard means lie in
  [0, ½] ⊂ [0,1].
- **D4.** UCB part inherits `Thm5_1_restricted`'s deterministic tie-rule restriction.
- **D5.** "Up to logarithmic factors" is the explicit factor 128√log(T²/δ) for UCB's tuning parameter
  δ ∈ (0,1) (e.g. δ = 1/T gives 128√(3 log T)).

## Recommended ledger text

COVERAGE row (Remark 5.12, `onlineRL.tex:2725–2729`):
> Restricted variant proved (lower bound unrestricted). `Remark5_12_lowerBound`: for 2 ≤ A ≤ T a fixed
> family of A mean vectors in [0,1]^A on which every measurable randomized history-dependent learner
> has expected pseudo-regret ≥ (1/16)√(AT) on some member (Gaussian N(0,1) noise, `bandits.tex:15–48`,
> `:66–70`). `Remark5_12_restricted`: additionally UCB's expected regret on every r ∈ [0,1]^A is
> ≤ 128√log(T²/δ) times that learner's regret, i.e. minimax-optimal up to log factors (`:296`);
> inherits Theorem 5.1's deterministic tie-rule restriction. Constant 1/16 is ours (remark gives none).

SOURCE-ISSUES, under `## Statement-index scope disclosures` (after the Theorem 5.1 line, :437):
> - Remark 5.12 (unlabeled, `onlineRL.tex:2725–2729`; numbered by the per-chapter remark counter) is an
>   informal claim and is indexed as its formal reading. `Remark5_12_lowerBound` (unrestricted): an
>   Ω(√(AT)) minimax lower bound, constant 1/16 and range 2 ≤ A ≤ T chosen by us, learners = seed from
>   any probability space (`Seed : Type`) plus arm maps measurable in (seed, past (arm, reward) pairs).
>   `Remark5_12_restricted`: the UCB optimality comparison (factor 128√log(T²/δ)) inherits the
>   deterministic tie-rule restriction of `Thm5_1_restricted` above. No source error.
