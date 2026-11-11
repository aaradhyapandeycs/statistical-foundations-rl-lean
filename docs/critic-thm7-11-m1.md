# CRITIC: Theorem 7.11 M1 (`thm:Berry-Esseen-linear`): `not_thm7_11_printed`, `_instWise`, `_allConvex`

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-08): this review was of the builder's pre-integration snapshot. The builder's three modules were integrated as `Formalization/TDInference/Definitions.lean` (Defs), `Formalization/TDInference/PrintedStatement.lean` (Printed) and `Formalization/TDInference/ZeroNoiseRefutation.lean` (ZeroNoise), and module names below are given under their integrated names; the file hashes quoted below are those of the reviewed snapshot. The required docstring fix R3 was applied at integration. Theorem 7.11 is recorded as a refutation of the printed statement under the readings named below, not as a proved result, and no statement-index entry suggests a proved Theorem 7.11. The later M2 review (docs/critic-thm7-11-m2.md) refuted the some-V₀ reading that this review lists as open, and its addendum text replaced the C43 addendum text at the end of this report. The review text below is otherwise unchanged.

I am an independent critic, not the builder. I read the source first (`inference.tex:40–210`, `prelim.tex:405–421`),
then AGENTS.md, SOURCE-ISSUES C43, the plan check, and only then the builder's Lean and notes. I edited nothing except
this file and the probe folder `<reviewer probe folder>/`. No paper was fetched.

## Verdict

**ACCEPT WITH DISCLOSURES.** `not_thm7_11_printed`, `not_thm7_11_printed_instWise` and `not_thm7_11_printed_allConvex`
are genuine refutations of the printed theorem under two named readings: (i) action-dependent rewards as printed,
with the undefined `r(s)` in Γ read as `r_π(s)`; (ii) every initialization V₀ (C̃ may depend on V₀). No Prop is
stronger than the printed text. The refutation is robust to every other choice (constant order, set class, RHS
coefficient). Required fixes R1–R4 are documentation and integration only; no Lean signature changes.

## Evidence (commands actually run, repo root, foreground, one at a time)

- Snapshot: the builder's snapshot hash list matches the snapshot files and the builder's live working files (`cmp` identical):
  TDInference711Defs `f8b6d4aa…8d7a`, TDInferencePrinted711 `76227d60…490b`, TDInferenceZeroNoise711 `9d048bc7…ef0612c`; these equal the final table of the builder's build log.
- Source pins: `inference.tex` `82707713…48f2`, `prelim.tex` `2d27bb72…31a5` (match the builder's private plan §0).
- Rebuilt from a copy, not the builder's oleans: `<reviewer probe folder>/*.lean` under a separate module prefix (only the
  module prefix in the import lines differs), compiled with
  `bash scripts/lean-local.sh -o <reviewer olean path>/<X>.olean <file>`: TDInference711Defs 7 s, TDInferencePrinted711 2 s,
  TDInferenceZeroNoise711 4 s, no errors, no output besides linters.
- Probe `<reviewer probe folder>/CriticProbe.lean` (output `critic-probe.out`, exit 0, 9 s):
  - `#print axioms` of `not_thm7_11_printed`, `not_thm7_11_printed_instWise`, `not_thm7_11_printed_allConvex`,
    `zeroNoise_violates`, `gaussCov_isProbabilityMeasure`, `lawProb_univ`: all `[propext, Classical.choice, Quot.sound]`.
  - `#print Thm7_11_printed`, `Thm7_11_printed_instWise`: elaborated bodies as read below (rpow exponents are real).
  - Critic-written checks at instance Z: Gaussian total mass 1; data law mass 1 at every T; the exact coefficient
    `printedRate … η₀ = 4√η₀ + 4√2/η₀` (as `√(4η₀)·2 + √2/(η₀/4)`); `A⁻¹ = !![3,1;1,3]` (so A is genuinely invertible
    and `Matrix.inv` is not the junk 0); `stepSize η₀ 1 = η₀` (first update is not the junk `0^(-2/3)=0`).
- Token scan of the three files: no `sorry`, `admit`, `axiom`, `opaque`, `native_decide`, `implemented_by`, `extern`,
  `unsafe`, `set_option`.
- Disclosure: a full project check was running two Lean compilers during my four short compiles, so up to three Lean
  processes ran briefly at once. Nothing under `Formalization/` or `.lake/build/lib/lean/Formalization*` was written.

## Check 1: fidelity of the refuted Props (hunting for "stronger than printed")

| Element | Source | Lean | Verdict |
| --- | --- | --- | --- |
| Sampling | i.i.d. s∼μ, a∼π(·|s), r=r(s,a), s′∼P(·|s,a) (:54–62), λ₀=min μ>0 | `pathWeight = ∏ μ(s)π(a|s)P(s′|s,a)`, `lawProb` exact finite sum; hyp `∀ s, 0<μ s` | faithful |
| Update | asynchronous, only V(s_t) changes (:72) | `tdStep` = `Function.update` at `x.1` | faithful |
| Step size / index (F1) | η_t = η₀t^{−2/3}, 0<η₀<1/4, t≥1 | V_{t+1} uses `ω t` and `stepSize η₀ (t+1)`; probe confirms η_1=η₀ | faithful |
| Averaging | V̄_T = T⁻¹Σ_{t=1}^T V_t (:82) | `Σ_{t<T} tdIter (t+1)` | faithful |
| Scaling/centring | √T(V̄_T − V^π) | `Real.sqrt T • (… − valueFixedPoint)`; `valueFixedPoint` is the unique Bellman fixed point | faithful |
| A | diag(μ)(I−γP_π) (:110) | `diagonal μ * (1 − γ•P_π)`, `P_π(s,s′)=Σ_a π(a|s)P(s′|s,a)` | faithful |
| Γ | μ(s)E_{s′∼P_π(·|s)}[(V^π(s)−(r(s)+γV^π(s′)))²] (:111) | `printedGamma` with r(s)=`policyReward`=r_π(s) | faithful under reading (i) |
| Gaussian | N(0, A⁻¹ΓA⁻ᵀ) | law of A⁻¹(√Γ⊙Z), Z std normal product; Cov = A⁻¹D^{1/2}D^{1/2}A⁻ᵀ = A⁻¹ΓA⁻ᵀ (Γ diagonal); probability measure (F2) | faithful, non-junk |
| RHS | (√(η₀/((1−γ)λ₀))Tr Γ‖Γ⁻¹‖ + √(Sκ(Γ))/((1−γ)λ₀η₀))T^{−1/3} + C̃T^{−1/2} | `printedRate` with ‖Γ⁻¹‖=1/min Γ, κ=max/min (correct for diagonal Γ ≻ 0) | faithful; `c·K·T^{−1/3}+Ct·T^{−1/2}` is equivalent to `c·(K T^{−1/3}+C̃T^{−1/2})` since Ct is existential |
| Quantifiers | `≲` universal c; C̃ "problem-related, independent of T" | `∃ c>0, ∀ instance V₀, … ∃ Ct>0, ∀ T≥1` | faithful; "polynomial" qualifier dropped (weakens) |
| Distance | sup over all convex sets | `_allConvex`: all convex; `Thm7_11_printed`/`_instWise`: closed convex only (F4) | weaker or equal, correct direction |
| Extra hyps | rewards in [0,1], γ∈[0,1) (setting) | enforced by `DiscountedMDP` fields | faithful |
| Γ ≻ 0 | ‖Γ⁻¹‖, κ(Γ) infinite otherwise | hypothesis `∀ s, 0<printedGamma` | definedness; weakens the Prop |

No element makes any refuted Prop stronger than the printed text. Universe restriction to `Type` also only weakens.
Beyond that, `zeroNoise_violates` holds for **every** real c, C̃ and η₀, so the refutation does not depend on the exact
coefficient: any finite K fails. The only load-bearing facts are: data law = δ₀; Gaussian nondegenerate (A invertible,
Γ_printed ≻ 0).

Reading dependencies (must be disclosed, R1):
- **(i) r(s) = r_π(s) with action-dependent rewards.** This is the only prelim-consistent reading (`prelim.tex:418`) and
  the printed setting has r_t = r(s_t,a_t) (:62), so it is not a strawman. But under a narrower reading in which rewards
  depend on the state only (or π is deterministic), the bracket equals the true TD error, Γ_printed = Γ_true, and
  instance Z is not admissible. Under the C43-corrected Γ, Z has Γ_true = 0 and the bound is vacuous (‖Γ⁻¹‖ = ∞).
  So M1 refutes the printed Γ formula, not a Berry–Esseen bound with the true noise covariance.
- **(ii) every V₀.** The source leaves V₀ unspecified. M1 uses V₀ = V^π. `Thm7_11_printed_someInit` (some V₀ per
  instance, e.g. V₀ = 0) is **not refuted in M1** (planned M2/R2).

## Check 2: non-vacuity, recomputed by hand

- V^π: r_π = (5/8, 1/8), P_π rows uniform, V = r_π + ¼(V₁+V₂) ⇒ V₁+V₂ = 3/2, V = (1, ½). Lean: `zValueFixedPoint`
  via the uniqueness characterization (not by assumption).
- TD error r(s,a)+½V(a) − V(s): (½+½−1, ¾+¼−1, 0+½−½, ¼+¼−½) = 0 on all four pairs ⇒ iterates from V^π never move on
  any positive-weight path (`tdIter_zV`), `lawProb … {0} = 1` (`lawProb_zero`), and `lawProb_univ = 1`.
- Γ_printed: brackets 1−5/8−½ = −1/8, 1−5/8−¼ = 1/8; ½−1/8−½ = −1/8, ½−1/8−¼ = 1/8 ⇒ Γ = ½·1/64 = 1/128 each. ≻ 0.
- A = [[3/8,−1/8],[−1/8,3/8]], det 1/8, A⁻¹ = [[3,1],[1,3]] (Lean probe). Gaussian({0}) = 0 via `Measure.map_apply`
  with `measurable_gaussMap`, preimage ⊆ ∏{0}, `noAtoms_gaussianReal`. Gap = |1 − 0| = 1 at every T ≥ 1.
- Hypotheses at Z: μ = (½,½) > 0; η₀ = 1/8 ∈ (0,¼); rewards ½, ¾, 0, ¼ ∈ [0,1]; γ = ½; Γ ≻ 0; {0} closed and convex.
- RHS: `exists_rhs_lt_one` takes T = N⁶ with N > |a|+|b|, giving a N⁻² + b N⁻³ ≤ (|a|+|b|)/N < 1, for all real a, b (F3).

## Check 3: axioms and forbidden tokens

PASS (see Evidence). The builder's axiom probe output agrees with my independent rerun.

## Check 4: library quality and the draft C43 text

Library quality is good: real definitions, F1–F4 all implemented (F2: `lawProb_univ`, `measurable_gaussMap`,
`gaussCov_isProbabilityMeasure`, and `gaussCov_singleton_zero` uses `Measure.map_apply`; F3: `zeroNoise_violates`,
`not_thm7_11_printed_instWise`; F4: closed sets plus `thm7_11_printed_allConvex_imp`). `trueGamma` matches C43's
corrected formula (unused in M1).

Draft C43 append (builder's status notes): numerically accurate, and it does say the some-V₀ reading is not machine-checked. It
overclaims in one place: "printed Theorem 7.11 is false" without naming readings (i)–(ii). It also misses a finding:
C43 describes Γ_printed as omitting the action-reward variance only, but in Z Γ_printed is **larger** than the truth.
The exact identity (with r(s)=r_π(s)) is

Γ_true,ss = Γ_printed,ss + μ(s)·[Var_{a∼π(·|s)} r(s,a) + 2γ·Cov_{a∼π, s′∼P(·|s,a)}(r(s,a), V^π(s′))].

In Z at s=1: 1/128 + ½(1/64 − 2·½·1/32) = 0. So the printed Γ also omits a cross term, which can be negative.

## Required fixes

- **R1.** The C43 addendum must name readings (i) and (ii), state that the state-only-reward (or deterministic-π)
  reading and the corrected-Γ statement are not refuted by Z, and state that the some-V₀ reading is open (M2). Use
  the text below.
- **R2.** C43's description must add the omitted cross term (identity above); the title "omits the reward variance
  across actions" is incomplete, because Γ_printed can be too large as well as too small. The proposed correction
  formula in C43 is already right.
- **R3.** At integration, qualify the docstrings of `not_thm7_11_printed` and the `TDInferenceZeroNoise711.lean` module header: "false under
  the every-V₀ reading with r(s) = r_π(s)" instead of an unqualified "as printed is false". This is documentation only;
  signatures unchanged.
- **R4.** Integration: rewrite the snapshot's module prefix to `Formalization.Ch7Rest.` in the imports, re-run the axiom audit on the integrated
  names, and record 7.11 in COVERAGE / named-result-status as "printed refuted (every-V₀, r_π reading); some-V₀ reading
  open; corrected theorem open". Do not add a `Thm7_11` statement-index entry that suggests a proved result.

## Optional findings

- O1. `zPrintedRate_pos` docstring writes `2√(4η₀)`; `4√η₀` is clearer (both correct; exact value checked in my probe).
- O2. `exists_rhs_lt_one` is a generic name inside a theorem-specific namespace; consider a more specific name or a
  general analysis file if reused.
- O3. The C43 text may note that the refutation holds for any finite coefficient and any constants c, C̃ chosen after
  the instance, so it does not depend on the printed powers of 1−γ, λ₀ or η₀.

## Required C43 addendum text

"Machine-checked (2026-11-08, `Formalization/TDInference/ZeroNoiseRefutation.lean`): Theorem 7.11 is false under
the reading in which rewards depend on (s,a) as printed at `inference.tex:62`, the undefined r(s) in Γ is r_π(s)
(`prelim.tex:418`), and the bound must hold for every initialization V₀ (`not_thm7_11_printed`; also with the
constants c and C̃ chosen per instance, `not_thm7_11_printed_instWise`, and over all convex sets,
`not_thm7_11_printed_allConvex`). Instance: S = A = 2, γ = 1/2, μ and π uniform, s′ = a deterministically,
r = (1/2, 3/4; 0, 1/4). Then V^π = (1, 1/2) and r(s,a) + γV^π(s′) = V^π(s) on every sample, so from V₀ = V^π the TD
iterates never move and √T Δ̄_T = 0 surely; the printed Γ is diag(1/128, 1/128) ≻ 0 and A = diag(μ)(I − γP_π) is
invertible, so N(0, A⁻¹ΓA⁻ᵀ)({0}) = 0. The convex distance is 1 at every T ≥ 1 (on the closed convex set {0}), while
the printed right-hand side tends to 0 for any finite constants. No CLT is used. The example also shows that the
printed Γ omits a cross term as well as the action-reward variance: Γ_true,ss = Γ_printed,ss + μ(s)[Var_a r(s,a) +
2γ Cov(r(s,a), V^π(s′))], and here Γ_true = 0 < Γ_printed. Not refuted by this example: the reading with state-only
rewards (or deterministic π), where Γ_printed equals the true noise covariance; the corrected statement (here
Γ_true = 0, so it is vacuous); and the reading with one fixed V₀ per instance (e.g. V₀ = 0), whose refutation is
planned but not yet machine-checked. Independently critic-reviewed. Not author-approved."

SHA-256 of this file: reported in the critic's hand-off message (computed after writing).
