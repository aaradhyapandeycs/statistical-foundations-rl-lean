# CHECK: finite-horizon minimax lower bound plan (independent plan check)

Public copy of the independent plan check; local paths removed. The plan checked here is the builder's private plan; it is not published.

Post-review note (added to this public copy, 2026-11-08): the plan was then built and independently reviewed in `critic-fhlb.md`, which reviewed the pre-integration snapshot; integrated into the library on 2026-11-08 (imports-only changes, one import rerouted through FiniteHorizonPolicyEvaluationConsumption for the frozen import-layering gate, plus the R1/R2/R4 docstring disclosures). The plan's proposed candidate number is written C₄₇ in this copy so that it is not linked to a source-issue entry: as this check recommends, no numbered source-error candidate was opened for it. `TRIAGE` refers to the lead's private work list, which is not published. The check text below is otherwise unchanged.

Checked file: the builder's private plan (not published),
sha256 `224da0553fe75a4ce2454fdf287c2baf31ec448a00cbc63795fa905f70652fb0` (verified, matches the brief).
Source read first: `generative_model_model_based.tex` :15–32 (generative protocol, known rewards),
:2540–2600 (Theorem 3.9 :2551–2570, display :2580–2583, minimax prose :2585).
No Lean/lake was run; nothing under `Formalization/` was touched. Scratch:
a private arithmetic script (exact/float arithmetic of the constants).

## Verdict: GO WITH FIXES

The mathematics is correct with the stated constants and genuinely yields H³/ε² per (s,a,h)
tuple, hence SAH⁴/ε² total under the book's protocol. All reused declarations exist with the
claimed meaning. The fixes concern naming/disclosure, C₄₇'s status, and one lemma shape.

## 1. Reading

- Locator: the claim is at MB:2585 (paragraph :2573–2585); :2589 is blank. Confirmed.
- Protocol: MB:25–28 + Theorem 3.9 ("sample size for every tuple (s,a,h) exceeds N") — non-adaptive,
  uniform N per (s,a,h), known rewards (:30). The book obtains SAH⁴/ε² as SAH × (per-tuple H³/ε²)
  (:2573–2583). So "N ≤ cH³/ε² per tuple ⇒ failure" is the faithful reading **of the book's
  protocol**. Caveat that must be disclosed: in this protocol the S and A factors are tautological
  (the hardness uses one copy and two actions); it is not the total-budget/non-uniform-allocation
  minimax statement of the cited literature. Acceptable as the formal reading, not as "the" minimax
  theorem; the docstring must say so.
- Accuracy measure: negation of Theorem 3.9's V-clause at h = 1, one state (s = copy-0 rewarding
  state). Correct and stronger than needed.
- Lean statement shape checked against `Ch3Definitions`: `samplingLaw`, `Samples`,
  `policyTrajectorySuffix (List.ofFn E) f 0` (= trajectoryValue of `controlled … (deterministicPolicy f)`
  after `drop 0`), `EnvironmentStage.optimalValue`. `ValueGap.lean` opens `EnvironmentStage`, so
  `optimalValue`/`controlled` there are the same constants. Quantifier order (c, c₁ before S,A,H,N,ε;
  E after piHat) is the right minimax order.

## 2. C₄₇ endpoint counterexamples

All four are mathematically correct (H = 1: transitions irrelevant; A = 1: one policy; S = 1:
trivial kernel; ε ≥ H: every policy is H-optimal since V ∈ [0,H]). But they refute only a literal
"for every S,A,H ≥ 1 and every ε ∈ (0,H] with universal constants" reading, which MB:2585 does not
print: the "(0,H]" range is attached to the **upper bound** (:2578), and the minimax sentence is an
order-of-magnitude prose claim with no domain. Not a strawman, but not a source error either.
**Required:** do not open a numbered Candidate C₄₇ as a source error; record the domain
(S,A,H ≥ 2, ε ≤ c₁H with existential c₁) in "Statement-index scope disclosures", exactly as
`Remark5_12_lowerBound` did for its chosen range `2 ≤ A ≤ T` ("No source error"). If the lead
still wants a C₄₇ entry for traceability, mark it informational/degenerate-scope, not an error.
Weakest honest domain: S ≥ 2, A ≥ 2, H ≥ 2, 0 < ε ≤ c₁H, c₁ existential — confirmed necessary
(each exclusion has a counterexample) and sufficient (the proof covers it).

Naming: **reject `_corrected`** — nothing printed is being corrected (Thm 3.7 got `_corrected`
because its displayed theorem domain was false). See §4 for unsuffixed vs `_restricted`.

## 3. Mathematics re-derived (all constants check)

- Family: with a⋆ ∈ {0,1} (`onlineLBq`, index 0 = source arm 1): a⋆=0 ⇒ q(0)=1/H−ε₀/(2H²), else 1/H;
  a⋆=1 ⇒ q(1)=1/H−ε₀/H², q(0)=1/H−ε₀/(2H²), else 1/H. Flip changes exactly row (h, state 0, action 1):
  1/H ↔ 1/H−ε₀/H². Needs A ≥ 2. Rewards σ-independent. Confirmed by reading the definition.
- Range: ε₀ = 2048ε ≤ H/2 ⇔ ε ≤ H/4096 = c₁H. `onlineLBq_bounds` then gives q ∈ [1/(2H),1/H];
  stay p = 1−q ∈ [1−1/H, 1−1/(2H)] ⊂ (0,1), p ≥ 1/2, so p(1−p) ≥ 1/(4H) for both orientations.
- KL: `bernoulli_toReal_klDiv_le_quadratic` gives (Δ)²/(p(1−p)) ≤ (ε₀/H²)²·4H = 4ε₀²/H³ per sample;
  N samples of one row ⇒ K ≤ 4Nε₀²/H³ = 2²⁴Nε²/H³ ≤ 1/16 for N ≤ 2⁻²⁸H³/ε². Other coordinates
  identical ⇒ KL 0. Correct.
- Gap: `onlineLBStages_value_gap` (j = 0), weights w_h = ε₀(H−h−1)/(16H²), h = 0..H−1 (w_{H−1}=0).
  Σ(H−h−1) = H(H−1)/2 ⇒ W = ε₀(H−1)/(32H) ≥ ε₀/64 (H ≥ 2). For deterministic π,
  1−π_h(g)(a⋆_h) = 1[f h g ≠ a⋆_h] ≥ 1[b_h ≠ σ_h] with b_h = (f h g = 1). Correct.
- `onlineLBq_gap` supplies the ε₀/(2H²) separation for both a⋆ values. Correct.
- Assouad + BH: overlap ≥ ½e^{−K} (`finite_exp_neg_klDiv_le_two_overlap`, full support on the Bool
  array) and test-error sum ≥ overlap (`finiteOverlap_le_test_error_sum`, orientation μ₀{test=true} +
  μ₁{test=false}, μ₀ = σ_h=false law): θ = ½e^{−1/16} ≥ 15/32 (e^{−x} ≥ 1−x). Pairing σ ↔ σ^{(h)}:
  avg_σ P_σ(b_h ≠ σ_h) ≥ θ/2, so avg_σ E_σ Z ≥ (θ/2)W, r = θ/2 ≥ 15/64 (≈0.2349). Correct.
- Reverse Markov (Z ∈ [0,W]): E Z ≤ tW + (1−t)W·P(Z ≥ tW) ⇒ P ≥ (r−t)/(1−t);
  t = 1/10: (15/64−1/10)/(9/10) = 0.14931 ≥ 1/8. Gap ≥ W/10 ≥ ε₀/640 = 3.2ε > ε (ε > 0). Correct.
- H⁴ genuinely obtained: per-stage KL budget N ε₀²/H³ ≲ 1 and loss ε₀ accumulated over H stages
  (each ε₀(H−h)/H², survival ≥ 1/4) ⇒ N ≍ H³/ε² per tuple, × SAH tuples. Matches Theorem 3.9's
  H³ log/ε² per tuple up to the log. Single-tuple Le Cam would give only H²/ε² (H³ total): agreed.
- 1/4 via Pinsker: needs r ≥ 0.325 at t = 1/10; with test-error sum ≥ 1−√(K/2), K ≤ ~0.24 suffices.
  Plan's claim that BH cannot reach 1/4 (r ≤ 1/4 < needed) is right.

## 4. Estimator class and probability level

- Probability 1/8 is fine: the prose gives no constant; Thm 3.7's 1/4 is a different statement.
- Deterministic-only is a **real restriction** for a minimax claim (minimax lower bounds quantify
  over randomized estimators; `Remark5_12_lowerBound`, the closest precedent for a prose lower
  bound, covers seeded learners). Randomization is nearly free here (see fix F2).
  **Required:** either cover randomized estimators (preferred; then name `Thm3_9_minimaxLowerBound`),
  or keep deterministic and name `Thm3_9_minimaxLowerBound_restricted` with a scope-disclosure line.

## 5. Lean risks and size

- All reuse targets exist with the claimed meanings: `onlineLBStages`, `onlineLBStage`, `onlineLBq`,
  `onlineLBq_bounds` (FamilyDefinitions.lean:41–148), `onlineLBStages_value_gap` (ValueGap.lean:414),
  `gadget_value_gap_quarter` (:323), `one_sub_inv_pow_ge_quarter` (:288),
  `onlineLBStages_values_nonGood` (:432), `indexedBernoulliLaw`(+`_atom_ne_zero`,
  `_toReal_klDiv`) (IndexedProductKL.lean), `klDiv_pi_eq_sum` (PrelimKL/KLArbitraryFinitePi.lean:13),
  `bernoulli_toReal_klDiv_le_quadratic` (BernoulliMeasure.lean:61; bound (q−p)²/(p(1−p)), denominator
  from the second argument), `bernoulliKLExpression_le_quadratic`, `finite_klDiv_map_injective`
  (FamilyKL.lean:21, needs μ ≪ ν), `finite_fullSupport_ac`, `finite_exp_neg_klDiv_le_two_overlap`
  (KLAffinity.lean:57, needs full support of both), `finiteOverlap_le_test_error_sum`
  (OverlapTesting.lean:15), `familyReconstruct`/`familySamplingLaw_eq_reconstructed_product`,
  `independentSeedLaw`. No existing Assouad lemma (grep: none) — new lemma justified.
- Main risk (agreed): `samplingLaw E_σ N = (indexedBernoulliLaw …).map reconstruct` over the full
  `(Fin H × Fin S × Fin A) × Fin N` index, with point-mass rows for absorbing states (incl. state 2m
  for odd S) and `exitRow` rows as Bernoulli push-forwards; the Thm 3.7 template file is 239 lines.
  The ⊤ instance clash (`local instance … := ⊤` in FiniteHorizonSamplingDefinitions vs
  `statementFinMeasurable` vs Mathlib's `Fin` instance) needs a bridging lemma; budget for it.
- Imports: `Online/LowerBound/*` imports only MDP and Mathlib — no cycle from Generative. The Ch3
  entry needs no Online definitions. OK.
- Size 0.8–1.3k lines is plausible; I would budget 1.0–1.5k including the bridge and the seed
  extension.

## Required fixes

- F1 (naming/disclosure). No `_corrected`. Name `Thm3_9_minimaxLowerBound` only if randomized
  estimators are covered; otherwise `Thm3_9_minimaxLowerBound_restricted`. Docstring must also
  disclose: (a) uniform per-tuple, non-adaptive protocol (the book's own), so the S·A factor is
  inherited from the protocol and not separately tested; (b) only copy 0 / actions {0,1} are used;
  (c) c₁ existential; (d) deterministic (or seeded) estimators given known rewards.
- F2 (Assouad shape). State the weighted Assouad lemma in **averaged** form
  (`(1/2^m) Σ_σ Σ_x μ_σ{x}·Z_σ(x) ≥ (θ/2) Σ w`) as finite sums over atoms (no Bochner integrals),
  with the existential and reverse-Markov steps as corollaries. The averaged form gives randomized
  estimators by exchanging the finite seed sum (or a general seed law via Fubini on finite data)
  with the σ-average, since θ is uniform over decoders — ~50–150 lines, not a new argument.
- F3 (C₄₇). Record the domain in "Statement-index scope disclosures" (Remark5_12 precedent), not as
  a numbered source-error Candidate; if a C₄₇ entry is kept, label it informational.
- F4 (docs). Fix TRIAGE 3.v locator :2589 → :2585; COVERAGE row for MB:2573–2585 must say
  "formal reading of prose, per-tuple protocol" and must not claim the cited domingues2021episodic
  total-budget/adaptive theorem.

## Answers to the plan's open questions

1. Per-tuple N ≤ cH³/ε² is the right reading of the book's protocol (MB:25–28, :2551–2583), with
   the disclosure in F1(a). A total/adaptive budget is a different, stronger theorem (optional §8).
2. Neither name as proposed by default: `_corrected` is wrong (no printed statement corrected);
   unsuffixed only with randomized estimators, else `_restricted` (F1).
3. 1/8 and existential c₁ = 1/4096 are acceptable. Deterministic-only is acceptable only under
   `_restricted`; matching 1/4 is unnecessary.
4. Re-derived: K ≤ 4Nε₀²/H³ ≤ 1/16; W = ε₀(H−1)/(32H) ≥ ε₀/64; r = ¼e^{−K} ≥ 15/64;
   P ≥ 0.1493 > 1/8; gap ≥ ε₀/640 = 3.2ε > ε. All correct.
5. Counterexamples correct; no separate source-error entry warranted (F3).
6. Yes. Using the book's own online family (onlineRL.tex:2512–3075, already formalized) with our own
   proof in place of the citation is acceptable; cite both in the docstring.
