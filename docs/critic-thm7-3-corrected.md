# CRITIC: corrected Theorem 7.3 (`thm:l1-lower-bound`, `robust_RL.tex:377–391`, C38)

Public copy of the independent critic report; local paths removed.

Critic: independent (did not build). Date 2026-11-07. Scope: `<builder working folder>/`
(Statement, Values, Testing, LowerBound, PAPER-PROOF.md, BUILD-LOG.md, AxiomProbe).

## Verdict: ACCEPT WITH DISCLOSURES

`Thm73Wip.thm7_3_corrected : Thm7_3_corrected` is a genuine, axiom-clean proof of the printed
Theorem 7.3 (all printed constants: `1/8`, `log 2`, `8192`, `c₀/256`, `0 < c₀ ≤ 1/8`,
`σ ∈ (0, 1-c₀]`, `γ ∈ [1/2,1)`) under exactly two extra hypotheses `2 ≤ card State`,
`2 ≤ card Action`. No junk-value or vacuity route was found. The disclosure (Finding 1) is that
the `S ≥ 2` hypothesis is not shown necessary, and in the Lean reading it appears unnecessary.

## Inputs reviewed (sha256, all match BUILD-LOG)

| file | sha256 |
|---|---|
| Thm73Wip/Statement.lean | 06cf28a02c3e2d73d9494d102869f5325e3ed7562b72e2d028aebe3de78ef2e4 |
| Thm73Wip/Values.lean | 1192c5300b8d554b3ef3dc206833cafe8709d9c81ce4efd9edc2dadbb0529ee5 |
| Thm73Wip/Testing.lean | 18b33d9c279c539403ff47bbc4edc9fbdc1bce50982e074b0c626ac08b6cf106 |
| Thm73Wip/LowerBound.lean | b9ff5156717f73e70f7d03eeb3b4f4834fbb0cc31ec046c671b42a91df7df497 |
| PAPER-PROOF.md | 8c43594e20dd2f44ea0c8a5587f62d2d070da2bf7910d13b8832bc60926e4093 |
| AxiomProbe.lean | 20adfd96ad7b5271c85b98f93cc9bcbb9780e169bc983a1a70ea9e32085b1bcf |

## Independent reconstruction of the printed statement (`robust_RL.tex:377–391`)

For TV `ρ`, any `(S, A, γ, σ, ε)` with `σ ∈ (0, 1-c₀]`, `0 < c₀ ≤ 1/8`, `γ ∈ [1/2,1)`,
`ε ∈ (0, c₀/(256(1-γ))]`: there exist two γ-discounted RMDPs `M₀, M₁` (on `S` states, `A` actions,
`(s,a)`-rectangular TV ball radius σ, :31–48), an initial distribution μ, and N generative samples
per (s,a) from each nominal kernel (:206–212), such that
`inf_{π̂} max_i P_i(V_i^{⋆,σ}(μ) - V_i^{π̂,σ}(μ) > ε) ≥ 1/8` whenever
`N ≤ c₀ log 2 / (8192 (1-γ)² max{1-γ,σ} ε²)`. This matches `Thm7_3_printed_at`
(already critic-accepted), including its ∀c₀ reading (the strongest of the three readings; it
implies the "sufficiently small c₀" reading).

## Checks performed (commands run from repo root, foreground, one at a time, no `-o`)

1. `bash scripts/lean-local.sh <builder working folder>/Thm73Wip/{Statement,Values,Testing,LowerBound}.lean`
   — all exit 0 (10s / 5s / 33s), zero warnings, zero errors. Outputs in
   `<reviewer probe folder>/reelab-*.out`. Olean mtimes postdate sources.
2. `bash scripts/lean-local.sh <reviewer probe folder>/CriticProbe.lean` — exit 0:
   * `critic_corrected_unfold : Thm7_3_corrected_at c₀ = (…) := rfl`, where the right side is
     the body of `Thm7_3_printed_at` extracted **mechanically by sed** from
     `Ch7PrintedStatements.lean` with only the line
     `2 ≤ Fintype.card State → 2 ≤ Fintype.card Action →` inserted. Definitional equality
     confirms the token-level diff.
   * `critic_corrected_wrapper : Thm7_3_corrected = ∀ c₀, 0 < c₀ → c₀ ≤ 1/8 → … := rfl`.
   * Concrete non-vacuity instance: `Fin 2 × Fin 2`, `c₀ = 1/8`, `γ = σ = 1/2`, `ε = 1/1024`,
     **N = 0**, every hypothesis discharged by `norm_num`/`positivity` and the conclusion
     obtained from `thm7_3_corrected`.
   * `#print axioms` for `thm7_3_corrected`, `hard_robustPolicyValue`, `hard_test_sum`,
     `hard_gap_event`, `critic_corrected_unfold`: `[propext, Classical.choice, Quot.sound]` only.
3. `grep` for `sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|set_option` in the
   WIP sources: no hits.
4. `diff` of the two `def` bodies: only the name line and the inserted hypothesis line differ.

## Findings

1. **Medium (disclosure) — `S ≥ 2` is not shown necessary; in the Lean reading it appears
   unnecessary.** `Thm73Wip/Statement.lean:30`; `docs/SOURCE-ISSUES.md#C38`.
   C38 machine-checks only the `A = 1` failure (`SingletonAction73.lean`); the `S = 1` case is
   argued "under the known-reward convention". But `Thm7_3_printed_at` does not encode that
   convention: `M₀, M₁` are chosen independently (rewards may differ) and the estimator sees only
   samples. Critic argument (paper only, **not Lean-checked**): for `S = 1`, `A ≥ 2`, take
   `r_j(a) = 1[a = a_j]`; the only row on a one-point type is the point mass, so the TV ball is a
   singleton, `V_j^{π,σ} = π(a_j)/(1-γ)`, `V_j^{⋆,σ} = 1/(1-γ)`; the data space is a singleton, so
   with `π := est(data)` one of `π(a₀), π(a₁)` is `≤ 1/2`, giving gap `≥ 1/(2(1-γ)) > ε` with
   probability 1 in that model. Hence the printed Lean Prop holds at `S = 1, A ≥ 2`, and the
   minimal formal correction is `A ≥ 2` alone. The corrected entry is still honest (it states
   exactly what is proved), so this is not a rejection, but it must be disclosed.
   Note in the builder's favour: `M₀, M₁` share the reward, so the proof is valid under the
   stricter known-reward reading too.
2. **Low — the builder's sanity probe is one-directional.** `AxiomProbe.lean:7–9`
   (`probe_printed_implies_corrected`) shows only `printed → corrected`, which would also pass if
   the corrected conclusion had been weakened. The decisive evidence is the definitional equality
   `critic_corrected_unfold` (see Check 2). Recommend adopting it, or an equivalent `rfl` check, in
   the integration probe.
3. **Info — estimator class (inherited from the accepted transcription).** `est` ranges over all
   functions `Samples → StationaryPolicy` (randomized stationary outputs, no measurability needed
   on the finite discrete data space). Externally randomized estimators and non-stationary output
   policies are not quantified. The proof gives `P₀(E₀) + P₁(E₁) ≥ 1/4` for every deterministic
   map, so the bound extends to externally randomized estimators by averaging (paper remark only).
4. **Info — definitional soundness verified (no surrogate or junk).**
   * Instances (`Values.lean:185–195`): rewards `0/1 ∈ [0,1]`; every row is a `FiniteDistribution`;
     `twoRow` clamps, but every use has `t ∈ [0,1]` proved (`hell01`, `hσlb`, `hlg`, and
     `σ ≤ 1` for `row(1-σ)`). `μ = pointMass s₀`. Discount `γ` (`rfl`).
   * `hard_robustPolicyValue` (`Values.lean:212`) is about the real `robustPolicyValue`
     (`sInf` of `trajectoryExpectedValue` of `withKernel M K` over all `K` with every row in
     `tvBall`, i.e. (s,a)-rectangular over **all** kernels). `sInf` is shown attained, so it is
     nonempty and bounded below: `le_antisymm` via `csInf_le` with lower bound `y` and witness
     `Kstar`, and `le_csInf`. The lower bound covers every admissible `K` (TV lemma plus
     sub-solution comparison with the true fixed point).
   * `robustOptimalValue` (`sSup`) is used only through `robustPolicyValue_le_optimal`
     (`TrapCore.lean:46`), which proves bounded-above (`1/(1-γ)`) and nonempty.
   * `samplingLaw` (`Ch3Definitions.lean:69`) is `Measure.pi` of the true nominal rows over
     `(S×A)×Fin N`, the genuine N-per-pair generative law. N = 0 gives the Dirac law on the
     singleton data space, and the proof never uses `N ≥ 1`.
   * Divisions: `yfun` denominators `(1-γ)(1-γ+γσ+γw) > 0`, the KL/χ² bound uses `lb(1-lb) > 0`,
     the N-bound denominator `8192(1-γ)²mε² > 0`, and `log 2 > 0`. No hypothesis is vacuous
     (concrete instance in Check 2).
5. **Info — math in PAPER-PROOF.md verified independently.**
   * Closed form: `y = γ(y + w d)` and `x = 1 + γ(x - σd)` with `d = 1/(B+γw)` give
     `V^{π,σ}(s₀) = γw/((1-γ)(B+γw))`. The adversarial kernel `row(ℓ(a)-σ)` / `row(1-σ)` is at TV
     distance exactly σ and valid since `σ ≤ ℓ_b`.
   * Gap: `γu ≤ u = c₀m/4 ≤ m/32 ≤ B/16` (`B ≥ m/2`), so
     `(B+γu)(B+γw) ≤ (17/16)²B²`. With `B ≤ 2m` and `γ ≥ 1/2`,
     `gap ≥ γBΔ/(2(1-γ)(17/16)²B²) ≥ 32Δ/(289(1-γ)m) = (512/289)ε > ε`. The Lean version proves
     the strict inequality via `(289/256)B² < 8γBm`.
   * (R4): `σ ≥ 1/2` gives `≥ (m/2)(3c₀/4) = 3c₀m/8`; `σ < 1/2` gives `≥ (3c₀m/16)(15/32)
     = 45c₀m/512`; both are `≥ c₀m/16`.
   * Testing: affinity `α^{2N}` (exact product factorization, only `(s₀,a₀),(s₀,a₁)` differ);
     `log α ≥ -KL/2 ≥ -χ²/2`, with `χ² ≤ 16Δ²/(c₀m)`;
     `2N·16Δ²/(c₀m) = 8192N(1-γ)²mε²/c₀ ≤ log 2`. Hence `α^{4N} ≥ 1/2`, overlap `≥ 1/4`,
     `P₀(E₀)+P₁(E₁) ≥ 1/4`, and `max ≥ 1/8`. Constant chain `2·16·256 = 8192` confirmed.
     Test inclusion: `π̂(a₀) > 1/2 ⇒ π̂(a₁) < 1/2` since `π̂(a₀)+π̂(a₁) ≤ 1` (`LowerBound.lean:279–284`).
6. **Info — integration not yet done (not a defect of the proof).** The modules live in
   `Thm73Wip.*`. On landing: move them to `Formalization/...`; add a self-contained
   `Thm7_3_corrected` entry to `Formalization/Statements/Ch7.lean` with a docstring citing
   `robust_RL.tex:377–391` and C38; add the `Ch7Proofs.lean` wrapper; update COVERAGE and C38
   (which currently says the correction "does not prove the cited bound"); run
   `python3 scripts/check.py`.

## Required edits (before or at integration)

R1. In the `_corrected` docstring and C38, state that `S ≥ 2` is assumed but not shown necessary.
    Under the Lean transcription, the `S = 1, A ≥ 2` case appears to hold by a direct argument
    (Finding 1); only `A = 1` is refuted. Preferred alternative: prove the `S = 1` case and drop
    the `S ≥ 2` hypothesis, making the entry `Thm7_3_corrected` with only `A ≥ 2`.
R2. Replace or augment `probe_printed_implies_corrected` with a definitional-equality probe like
    `critic_corrected_unfold` (Finding 2).
R3. Update C38's "does not prove the cited bound" sentence to reference the Lean proof once it
    is integrated, keeping "Not author-approved".
