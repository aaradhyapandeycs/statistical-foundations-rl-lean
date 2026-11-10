# Critic report: refutation batch (C34(1), C19 addendum, C22, C12) (2026-11-10)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of the library refutations `AsyncQ.not_Thm4_12_printed`, `AsyncQ.not_Remark4_3_printed` (`Formalization/ModelFree/AsyncQ/Thm412Refutation.lean`), `OfflineRL.not_Lemma6_5_printed` (`Formalization/OfflineRL/Lemma65Refutation.lean`), `OfflineRL.not_Lemma6_11_printed` (`Formalization/OfflineRL/Lemma611Refutation.lean`) and `OnlineRL.not_Lemma5_8_printed` (`Formalization/Online/Regret/Lemma58Refutation.lean`). Probes are local scratch files (`<local probe>`).

Integration note: all verdicts applied. The Remark 4.3 refutation was changed to ε = 1/4 as recommended, so it now also refutes the bare "mean error ≤ 2ε" reading (1 > 1/2) as well as the intermediate bound (23/64); the review below describes the reviewed ε = 1/2 version. The optional per-constant lemmas were added: `not_Thm4_12_printedAt` and `not_Remark4_3_printedAt` refute the claim for every fixed c₁, c₂ (the printed Props are now the ∃c₁∃c₂ closures of these `printedAt` Props, with unchanged bodies). The five modules are imported from `Formalization.lean` and covered by the axiom audit. The `printed_refuted` ledger entries use `kind: "boundary"` with the readings proposed below (Thm 4.12 also cites the per-constant lemma; Remark 4.3's reading states ε = 1/4), and the SOURCE-ISSUES notes for C12, C19, C22 and C34 and the matching COVERAGE rows were updated. These are library refutations, not statement-index entries.

Critic: independent (not the builder). Date 2026-11-10. Read-only review; no lake, no git.

## Compile and axioms

Each target file was copied verbatim into `<local probe>`
with `#print axioms` lines appended, then compiled with `bash scripts/lean-local.sh` (at most two
Lean processes at once). All four exit 0 with no warnings about `sorry`. Every refutation depends only on
`[propext, Classical.choice, Quot.sound]`:
`StatisticalRL.AsyncQ.not_Thm4_12_printed`, `StatisticalRL.AsyncQ.not_Remark4_3_printed`,
`StatisticalRL.OfflineRL.not_Lemma6_5_printed`, `StatisticalRL.OfflineRL.not_Lemma6_11_printed`,
`StatisticalRL.OnlineRL.not_Lemma5_8_printed`. Outputs: `<local probe>`.

## Is the "printed" Prop the entry minus its added premise?

- Thm4_12_printed versus Thm4_12_corrected (Ch4.lean:502): identical except that `0 < μmin` and
  `2 ≤ T ∨ 2 ≤ S·A` are dropped. `1 ≤ T` is kept. Remark4_3_printed versus Remark4_3_corrected
  (Ch4.lean:692): the same two premises are dropped and nothing else changes.
- Lemma6_5_printed versus Lemma6_5_sampleSplit_actualData_corrected: the only change is that `2 ≤ N`
  is dropped.
- Lemma6_11_printed versus Lemma6_11_restricted: the only change is that
  `1 ≤ log(SAT/δ)` is dropped.
- Lemma5_8_printed versus Lemma5_8_K2_corrected: `2 ≤ K` becomes `1 ≤ K`. I checked this with a diff.

## Fidelity to the printed source

- Thm 4.12 (generative_model_model_free.tex:2054–2086). The ∃c₁∃c₂∀ order is the strongest reading.
  The instance does not depend on c₁ or c₂, so every quantifier order fails. That holds on paper only:
  the Lean theorem refutes only the ∃∃∀ Prop. At T = 1, log 1 = 0 is the true value, so η = 0.
  Division by μmin = 1 is not junk, and t_mix = 0 is the true value. The other differences from the
  printed statement only add premises to the Prop (the explicit ergodicity constants, `IsLeast`,
  `1 ≤ T`), so dropping them would still leave a false statement. The algorithm text requires
  η_t ∈ (0,1) (:1937). Under that convention the instance is ill-posed, not a counterexample, which is
  the same situation as C35.
- Remark 4.3 (:2088–2090) has no formula. The refuted Prop is this project's reading of the remark,
  not printed text. The Lean proof refutes the intermediate bound ε(1−δ)+δ/(1−γ) using only the
  estimate error ≥ 1. With ε = 1/2 it does not refute the bare "≤ 2ε" form, because 1 = 2ε.
- Lemma 6.5 (offlineRL.tex:1104–1115). Faithful. The single-sample iid model is valid. log(32/31) > 0
  and the count 0 are both true values, so no junk value is involved. The lemma sits inside the proof
  of Thm 6.3, whose sample regime forces N ≥ 2. The refutation therefore applies to the lemma read on
  its own.
- Lemma 6.11 (:2292–2300). ≲ is read as ∃C first, which is correct. κ = 1−8η < 1, so the series is a
  genuine summable geometric sum and the tsum junk value is avoided. H = 1 because the ceiling of a
  positive number ≤ 1 is 1, not the junk H = 0. The result holds whether d⋆ is normalised or not
  (an unnormalised d⋆ gives an RHS ≤ 2.34C < 3C+1). This is the lemma read on its own: under
  Thm 6.8's hypotheses it holds (C22).
- Lemma 5.8 (onlineRL.tex:988–1005). Any formalization fails, because the claimed probability
  exceeds 1 − 0 = 1. The C8 completion, the tie rule and the c₁ regime are irrelevant to the failure.
  K = 1 lies in the proof's nontrivial regime K > ιSAH² = 0, and the side condition reads 0 ≤ 0.

## Classification

All four should be `kind: "boundary"`. In each case the instance is degenerate (T = 1 with SA = 1;
S·N = 1; S·A·T = 1; K = H = 1) and the repair restricts the domain. Thm 4.12 is additionally
ill-posed under η_t ∈ (0,1). None of the failures is driven by a junk value.

## Verdicts

- not_Thm4_12_printed: ACCEPT-WITH-FIXES.
  - Required: kind boundary, plus a note that under η_t ∈ (0,1) the instance is ill-posed.
  - Optional: a Lean lemma `∀ c₁ c₂, ¬ (instance claim)` that machine-checks the claim "every
    quantifier order".
- not_Remark4_3_printed: ACCEPT-WITH-FIXES.
  - Required: the ledger must call this the project's reading, not the printed text.
  - Recommended: use ε = 1/4. The budget at T = 1 holds for every ε, and the proof would then also
    refute the bare `E ≤ 2ε` (1 > 1/2).
- not_Lemma6_5_printed: ACCEPT, kind boundary.
- not_Lemma6_11_printed: ACCEPT, kind boundary.
- not_Lemma5_8_printed: ACCEPT, kind boundary.

## Proposed ledger wording

### printed_refuted entries (docs/named-result-status.json)

**thm:infinite-horizon-asyn**
- lean: [StatisticalRL.AsyncQ.not_Thm4_12_printed]
- kind: boundary
- paper: true
- reading: "T = 1 with S = A = 1 (log³T = 0, so the rate is 0 and Q₁ = Q₀; machine-checked for the
  ∃c₁∃c₂ Prop, and the instance is independent of the constants). Read with η_t ∈ (0,1) (:1937) the
  instance is ill-posed; domain repair T ≥ 2 or SA ≥ 2. μ_min = 0 (C34(2)) is a paper argument."
- issues: [C34]

**id:ch4-remark-4.3**
- lean: [StatisticalRL.AsyncQ.not_Remark4_3_printed]
- kind: boundary
- paper: false
- reading: "This project's reading (Remark4_3_corrected without the C34 premises; the remark has no
  formula), at the same T = 1, SA = 1 instance."
- issues: [C34]

**lem:sample-split-infinite**
- lean: [StatisticalRL.OfflineRL.not_Lemma6_5_printed]
- kind: boundary
- paper: false
- reading: "The standalone lemma at S·N = 1 (S = 1, A = 2, N = 1, δ = 31/32): the event is empty.
  Repair N ≥ 2; Theorem 6.3's regime implies it."
- issues: [C19]

**lemma:useful**
- lean: [StatisticalRL.OfflineRL.not_Lemma6_11_printed]
- kind: boundary
- paper: true
- reading: "Standalone, log(SAT/δ) < 1 (SAT = 1, δ = 9/10, γ = 1/8 − η, κ < 1): no universal constant
  works (Lean, for every C); κ ≥ 1 divergence is a paper argument. Theorem 6.8 unaffected."
- issues: [C22]

**lem:bound-T234**
- lean: [StatisticalRL.OnlineRL.not_Lemma5_8_printed]
- kind: boundary
- paper: false
- reading: "K = H = 1: the confidence 1 − 4log₂(KH)δ' equals 1 and no probability exceeds it. Repair
  K ≥ 2; the four inequalities and Theorem 5.2 are not refuted."
- issues: [C12]

### SOURCE-ISSUES notes (append one line to each)

- **C34(1):** "Machine-checked (2026-11-10): `AsyncQ.not_Thm4_12_printed`, `not_Remark4_3_printed`
  (`Formalization/ModelFree/AsyncQ/Thm412Refutation.lean`; instance with r = 0, Q₀ ∈ {0, 2}, for every
  c₁, c₂). This is a boundary case, not a junk value; under η_t ∈ (0,1) it is ill-posed. C34(2) is
  still a paper argument."
- **C19 addendum:** "Machine-checked: `OfflineRL.not_Lemma6_5_printed`
  (`Formalization/OfflineRL/Lemma65Refutation.lean`). Boundary case S·N = 1."
- **C22:** "The κ < 1 family is machine-checked for every C: `OfflineRL.not_Lemma6_11_printed`
  (`Formalization/OfflineRL/Lemma611Refutation.lean`). No tsum junk is used. Boundary corner SAT ≤ 2."
- **C12 (second endpoint):** "Machine-checked: `OnlineRL.not_Lemma5_8_printed`
  (`Formalization/Online/Regret/Lemma58Refutation.lean`). Boundary case K = H = 1. The K = 1 failure of
  Lemma 5.7 / W1 is still a paper argument."
