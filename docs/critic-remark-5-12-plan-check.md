# CHECK: Remark 5.12 plan (independent plan check, critic stance)

Public copy of the independent plan check; local paths removed. The plan checked here is the builder's private plan; it is not published.

Post-review note (added to this public copy, 2026-11-08): F5's planned `GaussianBanditDefinitions.lean` was not created. To respect the frozen import-layering gate (no new import edge from `Formalization/Statements/Ch5.lean`), the definitions were appended to the existing definitions module `Formalization/Online/Bandit/UCBDefinitions.lean`; the proof modules are `Formalization/Online/LowerBound/GaussianBandit{Measurability,Shift,ChangeOfMeasure,KL,Minimax,UCBOptimal}.lean`. The check text below is otherwise unchanged.

Date: 2026-11-08. Plan checked: the builder's private plan,
sha256 `34ff97535e156d1d396d632190cf2b70ef36a9c3f3e7edc65d6d1626d900a381` (verified, matches).
No Lean or lake was run. Nothing under `Formalization/` was touched. No paper was fetched.
Source read first: `onlineRL.tex:2680–2740`, `bandits.tex:1–75` and `:250–320`,
`nowfnt.cls:1331–1337`. Then the plan. Then the repo files and the pinned Mathlib (a read-only
checkout at the pinned rev).

## Verdict: GO WITH FIXES

The mathematics is correct; I re-derived every step and constant independently. The reading is
faithful, and the learner class is general enough. The fixes concern the index naming and scope,
one wrong API step, and a few smaller statement and tooling points. None of them blocks starting
the builder.

## Required fixes

- **F1 (naming and scope; see Q1 and Q3).** A `Remark5_12` entry that holds only the lower bound
  would label a lemma with a remark whose literal claim is "minimax optimality of the UCB
  algorithm". The lower bound alone is not that claim. Use two entries:
  - `Remark5_12_lowerBound` (no restriction): the new mathematical content, ∀ L ∃ μ ∈ [0,1]^A,
    E Regret ≥ (1/16)√(AT) for T ≥ A ≥ 2.
  - `Remark5_12_restricted`: UCB's worst-case regret ≤ 128·√log(T²/δ) × the minimax lower bound,
    for every deterministic tie rule. It inherits Theorem 5.1's tie-rule restriction, so it needs
    a `_restricted` suffix. It points to the existing
    `SOURCE-ISSUES.md#statement-index-scope-disclosures` entry; add one line there for
    Remark 5.12.

  Alternatively, a single `Remark5_12_restricted` entry that is the conjunction of both. Either
  way, the COVERAGE status must read "Restricted variant proved (lower bound unrestricted)", not
  "Printed result proved".
- **F2 (Step C API).** `toReal_klDiv_of_measure_eq` (KullbackLeibler/Basic.lean:157) gives only
  `(klDiv P Q_j).toReal = ∫ llr`. It does not give `klDiv = ofReal(...)`, because `klDiv` could be
  `⊤`. Use this route instead:
  1. Get `Integrable (llr P Q_j) P` from `integrable_llr_tilted_right` (LogLikelihoodRatio.lean:190).
     It takes `llr P P` integrable, which holds because `llr_self` makes it a.e. 0.
  2. Then `klDiv_of_ac_of_integrable` (Basic.lean:62) gives `ofReal(∫ llr + 1 − 1)`.

  Also note that `Measure.tilted` is `withDensity (ofReal (exp f / ∫ exp f))` (Tilted.lean:42). To
  identify it with `withDensity (exp f)` you need the *real* normalizer to equal 1, obtained from
  the lintegral via `ofReal_integral_eq_lintegral_ofReal`. Similarly, `log (∫ exp f) = log 1 = 0`
  in `integral_llr_tilted_right` needs that real identity.
- **F3 (name provenance).** `integral_apply_stdGaussianPi` is not in Mathlib. It is a repo lemma
  (`Formalization/Probability/StdGaussianPi.lean:110`) about `stdGaussianPi`, not about
  `gaussianNoiseTable`. For the predictable-zero-mean step, the simpler route is Fubini/marginal:
  the indicator does not depend on row `s`, so integrate row `s` first and use
  `integral_id_gaussianReal`. This avoids `iIndepFun_pi`, which needs the seed to be included in
  the independence family. It also reuses the `lmarginal` pattern of `GaussianPredictableExp.lean`.
- **F4 (statement detail).** Add an `Integrable regret (seedLaw.prod table)` conjunct to the
  lower-bound Prop, for parity with `Thm5_1_restricted` and so readers can see that the integral
  is not a junk value. (For a *lower* bound, a junk value of 0 would make the claim false, not
  vacuous, so this is for clarity and not soundness.) Also prefer the stronger,
  learner-independent family form, which the proof gives at no extra cost:
  ∃ μ⁽⁰⁾,…,μ⁽ᴬ⁻¹⁾ ∈ [0,1]^A, ∀ L, ∃ i, bound. If the simpler ∀ L ∃ μ form is kept, the docstring
  must say that it is the inf–sup reading.
- **F5 (statement-index hygiene).** `Statements/Ch5.lean` may import only definition modules.
  `GaussianBanditDefinitions.lean` must therefore contain only definitions: the learner structure,
  `history`, `armAt`, `regret`, and the instance family. The measurability proofs go in the
  separate file the plan already lists. The learner's `arm_meas` field is a Prop field, which is
  fine.

## (1) Reading

- **Content.** "Minimax optimality of UCB" (OL:2725–2729) is defined at BA:296 as
  "minimax-optimal up to logarithmic factors", and BA:296 cites a matching lower bound. The
  content to establish is therefore an Ω(√(AT)) lower bound for all algorithms, uniform over means
  in [0,1]^A, together with Theorem 5.1. The plan's (LB) is the faithful, non-strawman core.
  - The remark gives no constant, so any explicit c > 0 is acceptable.
  - The range T ≥ A ≥ 2 matches Theorem 5.1's hypotheses, which is what "optimal" compares
    against.
  - It is not a strawman: the bound holds for every learner, and the witness is inside the
    printed mean class. The witness means lie in [0, 1/2].
- **Noise model.** The iid N(0,1) noise table and means r(a) ∈ [0,1] are exactly BA:15–42. The
  learner seeing only R_{a_t,t} is BA:47–48. The pseudo-regret T r⋆ − Σ r(a_t) is BA:66–70.
  `gaussianNoiseTable` (UCBDefinitions.lean:29) is the same object `Thm5_1_restricted` uses.
- **Learner class.** It consists of a seed from an arbitrary probability space, independent of
  the noise, plus measurable deterministic causal maps of the past (arm, reward) pairs.
  - This covers every randomized history-dependent algorithm whose induced law is defined. Per-
    round randomness reduces to a single seed.
  - Measurability is the only restriction, and it is needed for "E Regret" to mean anything; the
    docstring should disclose it.
  - The class strictly contains Lemma 5.21's finite-seed `BanditLearner`, and UCB with any
    deterministic tie rule (Seed = Unit).
  - L may depend on T and A (quantifier order ∀ A T ∀ L), which is correct.

## (2) Policy: should an unnumbered remark be indexed?

- The remark *is numbered*. In `nowfnt.cls:1335` remarks have their own per-chapter counter,
  `\newtheorem{remark}{Remark}[chapter]`, not shared with theorems or lemmas. Counting the live
  `\begin{remark}` environments in Chapter 5:
  - OL lines 425, 486, 660, 790, 959, 963, 1096, 1330, 1746 and 2043. Lines 1242 and 1411 are
    commented out, so they do not count.
  - BA:279, input at OL:202.

  That is 11 remarks before this one, so it is **Remark 5.12**. The plan's count is confirmed.
  There are no `\iffalse` or comment blocks in OL before line 2730.
- **Policy recommendation.** Treat a numbered remark (or prose claim) that makes a definite
  mathematical assertion as a "source result" once COVERAGE records it proved. Index it under the
  environment's own name, `RemarkN_k`, with `_restricted`/`_corrected` suffixes under the same
  rules as theorems. Index unnumbered prose claims under their host result with a descriptive
  suffix, as already done for `Thm3_2_approxPlanner_positiveN` and `Thm3_2_planningIterations`
  (Ch3.lean:249–301; COVERAGE rows 76–77).

  This is consistent with AGENTS.md, which puts all "substantive mathematical claims" in scope. A
  docstring must say that the Prop is the formal reading of an informal remark, and cite
  OL:2725–2729, BA:296 and BA:258–277. Naming: see F1.

## (3) Mathematics (re-derived)

- **Family.** Take μ⁽⁰⁾ = (ε/2 at arm 0, 0 elsewhere), and for j ≥ 1, μ⁽ʲ⁾ = μ⁽⁰⁾ + ε·e_j.
  - Instances 0 and j differ only at arm j.
  - In instance j, every a ≠ j has gap ≥ ε/2 (exactly ε/2 or ε).
  - So Regret_j ≥ (ε/2)·#{s : a_s ≠ j} pointwise. For A = 2 this still works: μ⁽¹⁾ = (ε/2, ε).
- **Change of measure.** Let f_j = Σ_s 1{a_s⁽⁰⁾ = j}(ε z_{s,j} − ε²/2), with arms computed under
  instance 0.
  - Under exp(f_j)·P, the row-s coordinate z_{s,j} at rounds where a_s⁽⁰⁾ = j becomes N(ε,1),
    conditionally on the past. Unobserved coordinates keep N(0,1), and the arm choice is
    predictable.
  - The observed reward at arm j under instance-0 dynamics is then 0 + N(ε,1), which is
    μ⁽ʲ⁾(j) + N(0,1).
  - So the law of (σ, H_T⁽⁰⁾) under Q_j equals the law of (σ, H_T⁽ʲ⁾) under P. The inductive
    proof (integrate out the last row, apply the 1-D shift identity
    φ(y+c) ↔ e^{cy−c²/2}, with c = ε·1{a=j}) is correct.
  - Taking g = 1 gives ∫ e^{f_j} dP = 1.
- **KL.** KL(P‖Q_j) = ∫ log(dP/dQ_j) dP = −E_P f_j = Σ_s E_P[1{a_s=j}(ε²/2 − ε z_{s,j})]
  = (ε²/2) E_P N_T(j). This holds because 1{a_s=j} is a function of (σ, rows < s) and
  E z_{s,j} = 0.
  - The direction KL(P₀‖P_j) matches `reverseFano_test_error_lower`'s `hKL`
    (ReverseTest.lean:84). Correct.
  - Σ_{j≥1} N_T(j) ≤ T, so the sum is ≤ ε²T/2 = B. The adaptive (observed-only) density is
    essential; the full-table KL would cost Mε²T/2. Correct.
- **Reverse Fano.** The lemma gives avg_j Q_j(ψ ≠ j) ≥ 1 − 1/A − √((A−1)B/(2A²)), using
  M = A − 1 and (M+1)² = A². Take ψ_s = a_s⁽⁰⁾ and g = 1{arm_s(σ, H_s) ≠ j}; then
  Q_j(ψ_s ≠ j) = P(a_s⁽ʲ⁾ ≠ j).
  - Scalar check: ε = ½√(A/T) gives B = A/8, and (A−1)(A/8)/(2A²) = (A−1)/(16A) < 1/16, so
    √ < 1/4. Also 1 − 1/A ≥ 1/2 for A ≥ 2. The bound is ≥ 1/4. `fano_quarter` is a trivial
    scalar lemma.
  - A ≥ 3 variant: ε² = 4A/(9T) gives B = 2A/9, which is exactly `fano_third`'s hypothesis
    (TestingTools.lean:161). Then ε = (2/3)√(A/T) ≤ 2/3, and the regret is
    ≥ εT/6 = √(AT)/9. Correct.
- **Regret.** avg_j E_j Regret ≥ (ε/2) Σ_s avg_j P(a_s⁽ʲ⁾ ≠ j) ≥ (ε/2)(T/4) = εT/8 = √(AT)/16.
  Max ≥ average: the real `Finset.exists_le_of_sum_le` is the `to_additive` of
  `exists_le_of_prod_le'` (Algebra/Order/BigOperators/Group/Finset.lean:552).
- **Means in [0,1].** The means lie in [0, ε], and ε = ½√(A/T) ≤ 1 iff T ≥ A/4. Under T ≥ A,
  ε ≤ 1/2. Fine.
- **Export 3** (the Gaussian analogue of Lemma 5.21 at horizon t, with ε²t ≤ 4A/9) is correct
  for the same reasons: a_t reads only rows < t, so B = ε²t/2 ≤ 2A/9. It is optional; skip it
  unless it costs nothing given a general-T Step B.

## (4) Mathlib names (pinned copy, read-only grep)

These exist:

| Declaration | Location |
|---|---|
| `Measure.tilted` | Tilted.lean:42 |
| `tilted_apply'` | Tilted.lean:101 |
| `isProbabilityMeasure_tilted` | Tilted.lean:126, needs `NeZero μ` |
| `absolutelyContinuous_tilted` | Tilted.lean:283 |
| `integral_llr_tilted_right` | LogLikelihoodRatio.lean:197; hypotheses `μ ≪ ν`, `Integrable f μ`, `Integrable (exp ∘ f) ν`, `Integrable (llr μ ν) μ` |
| `integrable_llr_tilted_right` | LogLikelihoodRatio.lean:190 |
| `llr_self` | LogLikelihoodRatio.lean:41, a.e. statement |
| `toReal_klDiv_of_measure_eq` | KullbackLeibler/Basic.lean:157, toReal only (F2) |
| `klDiv_of_ac_of_integrable` | KullbackLeibler/Basic.lean:62 |
| `gaussianReal_map_add_const` | Gaussian/Real.lean:278 |
| `rnDeriv_gaussianReal` | Gaussian/Real.lean:240 |
| `gaussianPDFReal_def` | Gaussian/Real.lean:52 |
| `measurePreserving_piFinSuccAbove` | Constructions/Pi.lean:793 |
| `lintegral_withDensity_eq_lintegral_mul` | WithDensity.lean:364 |
| `iIndepFun_pi` | Independence/Basic.lean:783 |

Not in Mathlib: `integral_apply_stdGaussianPi`, which is a repo lemma (F3). Repo names
confirmed:
- `lintegral_prod_predictable_le_one` (GaussianPredictableExp.lean:22)
- `lintegral_exp_gaussian_coord` (GaussianPredictableExp.lean:112)
- `gaussianNoiseTable` and `extendNoise` (UCBDefinitions.lean:29, 61)

**Junk values.**
- The regret is bounded by T·max μ, so it is integrable once it is measurable. Measurability rests
  on R2 (the dependent `Fin.snoc` history).
- `f_j` is integrable because it is bounded by ε Σ|z| plus a constant.
- `exp f_j` is integrable from lintegral = 1.
- The tilt is a probability measure.

## (5) Optional optimality corollary

Include it, as `Remark5_12_restricted` (F1). It costs about 40 lines and is the literal content
of the remark. The arithmetic 8√(ATℓ) = 128√ℓ·(1/16)√(AT) is correct, with ℓ = log(T²/δ) > 0
because T ≥ 2 and δ < 1. It inherits the deterministic-tie restriction of `Thm5_1_restricted`,
which is disclosed already. Do not build a `ucbAction = armAt` bridge; the inequality does not
need it.

## (6) Size and risks

- **Estimate.** 850–1300 lines is plausible. Budget up to about 1600 lines because of R1 and R2.
- **R1.** For the induction, fixing T and peeling rows of the fixed table with
  `lmarginal`/`piFinSuccAbove` over k ≤ T is safer than induction on the type-changing T. Prefer
  the plan's fallback as the primary route. History on ℕ via `extendNoise` is fine.
- **R2.** The dependent `Fin t → Fin A × ℝ` history is a real measurability cost. An ℕ-indexed
  history with a causal field is acceptable only if the critic checks that the field enforces
  causality.
- **Extra risk.** Do the Tonelli step over an arbitrary `Seed` at the level of the product measure
  directly. f_j and Q_j live on Seed × table. This avoids per-σ measurability of sections of
  `llr`.

## Answers to the plan's open questions

1. **Naming.** Index it; the remark is a numbered environment (Remark 5.12, own counter). Use
   `Remark5_12_lowerBound` plus `Remark5_12_restricted` (or the conjunction as
   `Remark5_12_restricted`), not a bare `Remark5_12` holding only the lower bound. The
   up-to-log reading is faithful (BA:296) and by itself needs no suffix; the tie restriction does.
2. **Learner class.** Yes. It is the right class, with measurability disclosed. It contains the
   Lemma 5.21 class and UCB.
3. **Export 2.** Include it as the restricted optimality entry. The lower bound is the new content;
   optimality is the remark's literal claim.
4. **Method.** Acceptable. The same family shape, per-round testing and reverse Fano against the
   reference, with the Bernoulli KL replaced by the Gaussian ε²/2 per observed pull, is exactly
   the adaptation the remark describes. Coverage depends on the result in any case.
5. **Constant and range.** Use 1/16 on T ≥ A ≥ 2 as the main statement; it matches Theorem 5.1's
   range. The 1/9 variant for A ≥ 3 is optional and not needed.
