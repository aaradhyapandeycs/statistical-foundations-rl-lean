# CRITIC — trivial batch A (Ch6), independent review

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-09): this critic reviewed the pre-integration snapshot; the seven entries were integrated into the library on 2026-11-08/09. R1 was applied: the line-892 entry is named `Lemma6_2_iterationCount_restricted` (reviewed below under its snapshot name `Lemma6_2_iterationCount_corrected`), and its docstring, its `COVERAGE.md` row and the scope-disclosure bullet in `SOURCE-ISSUES.md` say that the claim is OPEN for γ < 1/2 (neither proved nor refuted; C10's instance does not refute it). F1: the duplicate-label observation was dropped. F2: the Remark 6.3 (ii) zero-reward witness and tie choice are disclosed in the docstring, the COVERAGE row and a scope-disclosure bullet. F4: the COVERAGE wording follows R1. §4: Example 6.1 has a COVERAGE row only and no named-result ledger record. Snapshot files map to the integrated locations as follows: `GaussianTailLower.lean` → `Formalization/Probability/GaussianTailLower.lean`; `ConcentrabilityFacts.lean`, `VILCBIterationCount.lean`, `BanditExample.lean` → the files of the same names in `Formalization/OfflineRL/`; `StatementsCh6A.lean` → the entries in `Formalization/Statements/Ch6.lean`; `StatementsCh6AProofs.lean` → the `_holds` wrappers in `Formalization/Statements/Ch6Proofs.lean`. `CHECK` refers to the independent plan check, published as `critic-trivial-batch-plan-check.md`; `DRAFTS` refers to the builder's private notes. Short file names below refer to the reviewed snapshot files, and the file hashes are those of the snapshot. The review text below is otherwise unchanged.


Critic: independent critic agent. Did not build these items. Read-only on builder files.
Target: the builder's read-only pre-integration snapshot (private).

## 0. Snapshot integrity
`shasum -a 256 -c` against the builder's snapshot hash list: all 6 OK. The builder's live working files are byte-identical
(`cmp`) to the snapshot. Hashes:
- BanditExample.lean 5637504024a556b0366087005b35eb3f44f8372a746b95ec2a68519d9a40a7e2
- ConcentrabilityFacts.lean da7d7eefb318d5098a04fbb9abb0c59c5ab87870b587fecec708281854b93df0
- GaussianTailLower.lean 55708598a138b6f64a1eb088ccb08e02d0a8c1659b835cb616918066ead10603
- StatementsCh6A.lean 1b29f0558843647148596687a10e29bccbec5c202e92362bf6405573b033c823
- StatementsCh6AProofs.lean f57461cb293bcf99b477c3e680d318638713867a46fc64c5a217fbcf0c3af72d
- VILCBIterationCount.lean 11bb76488d93a583e3ec89bd309b9c0a32c604f92c8e10ddd352d721039bf5fd

Source read first: `source/upstream/tex/chapters/offlineRL.tex` 125–205, 230–285, 318–420, 868–895.

(Findings appended below as the review proceeds.)

## 1. Independent build and axioms
Snapshot copied to the reviewer's private probe folder with only import-prefix rewrites (builder's working prefix ->
reviewer's private prefix), then compiled one at a time, foreground, with `bash scripts/lean-local.sh -o <reviewer olean folder>/<X>.olean
<probe folder>/<X>.lean`: GaussianTailLower (14s), ConcentrabilityFacts
(11s), VILCBIterationCount (5s), BanditExample (14s), StatementsCh6A (12s), StatementsCh6AProofs (13s), all exit 0.
Probe `Probe1.lean` in the reviewer's private probe folder (exit 0): `#print axioms` for all seven `_holds` and both
tail lemmas = {propext, Classical.choice, Quot.sound}. Matches builder `axiom-probe.out`.

Forbidden tokens (grep `sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque|set_option|decide`):
none in the four library files or the statement files. X1: no library file imports `Statements.*` or cites a
`_holds`; `VILCBIterationCount` uses `Input.lem_monotone_contraction_corrected`. Statement file imports are the four
allowlisted definition modules only; it contains no proofs. Wrappers are one-line applications of library exports.

## 2. Per-entry review

### Example6_1 — ACCEPT
- Source (OFF:348–355): A={1,2}, r₁=1, r₂=0, a_i=1 (i<N), a_N=2, `E[r⋆ − r_{a^emp}] ≥ 0.075` for any N ≥ 2;
  r̄ is `eq:empirical-best-arm-offline` (:323–339). Lean: `Fin 2` with arm 1 ↦ 0, design `i<N−1 ↦ 0`, last ↦ 1,
  `empiricalArmMean` = Σ_{a_i=b}(r(a_i)+z_i)/n_b, noise `Measure.pi (gaussianReal 0 1)`. Faithful.
- Lower Lebesgue integral: Mathlib's `∫⁻` of an arbitrary f is the sup of integrals of measurable simple minorants,
  so `0.075 ≤ ∫⁻` says a measurable minorant of the regret already has mean ≥ 0.075. For a measurable selector the
  integrand is bounded and `∫⁻ ofReal f = ofReal (∫ f)` (probe: `ofReal_integral_eq_lintegral_ofReal`), so it is
  exactly the printed expectation; for non-measurable selectors it is the inner integral, the strongest reading.
  Not junk: the integrand `ofReal(1 − r(sel z)) ∈ {0,1}` is nonnegative because r⋆ = r 0. Stronger than printed
  (every tie rule; printed proof silently uses P(tie)=0).
- Non-vacuity: probe proves an empirical-best selector exists for every N, so the `∀ sel, argmax → …` premise is
  satisfiable.
- Tail lemma: `gaussianReal_Ioi_one_ge : ofReal 0.15 ≤ gaussianReal 0 1 (Set.Ioi 1)`; probe confirms by `rfl`
  ascription that the arguments are mean `(0:ℝ)`, variance `(1:ℝ≥0)`, set `(1,∞)`, i.e. P(Z>1) for Z∼N(0,1).
  Printed proof uses P(r̄₂ ≥ 1) ≥ 0.15; open vs closed ray is immaterial (atomless) and the Lean route uses
  {Σ_{i<N−1} z_i ≤ 0} ∩ {z_{N−1} > 1} (A1-a). Numerics re-checked: four tangent windows give certified
  (95/192·0.7762)/2.5067 = 0.15321 ≥ 0.15 (true P(Z>1)=0.158655). Exact regret lower bound ½·P(Z>√((N−1)/N)) is
  0.1199 (N=2) … 0.0794 (N→∞), so 0.075 is genuinely true and not weakened.

### Remark6_5 — ACCEPT WITH DISCLOSURES (F5 reading)
- Source (:413–415) is informal ("≈ for large enough N", "with high probability"). Reading: δ∈(0,1),
  N−1 > 8 log(8/δ), probability ≥ 1−δ of {r₂^lcb ≤ 0, |r₁^lcb − 1| ≤ 2√(2log(8/δ)/(N−1)), r₂^lcb < r₁^lcb}.
  Penalty `armRadius (card (Fin 2)) δ n = √(2 log(8/δ)/n)` = `eq:penalty-bandit-illustrate` with A=2. Both counts
  positive, so `lcbFallback` = active pseudocode (C18 not reached). Hypotheses satisfiable (e.g. δ=½, N=100).
  Threshold is exactly what makes 1−2b₁ > 0 ≥ r₂^lcb. `.real` of the event: the event is measurable
  (finite sums of coordinates), so no outer-measure weakening. Reading is a disclosure, not a source error.

### Remark6_4 — ACCEPT WITH DISCLOSURES (F5 reading)
- d^b read as design frequency n_b/N (the example's design is deterministic, so the source's i.i.d. d^b does not
  literally exist). Value: b=0 gives ofReal 1/ofReal((N−1)/N) = N/(N−1); b=1 gives ofReal 0/ofReal(1/N) = 0. The
  conjunct `N/(N−1) → 1` renders "exceedingly close to 1". Docstring names the reading. Fine.

### Eq_defn_Cstar_bandits — ACCEPT
- `⨆ b, 1{b=a⋆}/d{b} = (d{a⋆})⁻¹` in ℝ≥0∞ for any finite arm type and any measure. 0/x = 0 including x = 0
  (matches :138 convention), 1/0 = ⊤ (probe). Generalizes the printed identity (no normalization needed).
  Note: with an exotic `MeasurableSpace` `d {b}` is an outer measure value; the identity is algebraic, so harmless.

### Remark6_2 — ACCEPT
- Stated for every stationary policy π, every ρ and every probability vector d^b; `discountedJointOccupancy` is the
  (1−γ)-normalized occupancy (`discountedJointOccupancy_sum = 1`), as the printed Σd⋆ = 1 requires. x/0 = ⊤ only
  helps the bound and matches the natural convention; 0/0 = 0 as printed. Strictly covers every optimal
  deterministic π⋆ (any tie). Follows check advice A5.

### Remark6_3 — ACCEPT WITH DISCLOSURES
- (i) for every π: faithful ("Clearly ≤"). (iii) C_clipped ≥ 1/S for every π: true (added per check advice; not
  printed, conclusion-only extra). The li2024settling sentence (:184) is honestly excluded.
- (ii) existence via `clippedWitnessMDP`: discount 0, all transitions to s₀, **all rewards 0**, ρ = δ_{s₀},
  d^b = δ_{(s₀, optimalGreedyAction s₀)}. Valid instance and correct value 1/S. Disclosure F2 below: the witness is
  fully degenerate (every policy is optimal), so "C⋆_clipped" there depends on the library's tie choice
  `optimalGreedyPolicy`; another optimal deterministic policy gives ⊤. The printed sentence is existential and the
  source's π⋆ is itself tie-ambiguous, so this is acceptable, but a witness with a unique optimal action would be
  more robust (non-blocking).

### Lemma6_2_iterationCount_corrected — ACCEPT WITH DISCLOSURES, R1 required before landing
- Lean Prop: on 1/2 ≤ γ (γ<1 is a field), ∃ unique fixed point Q⋆ of `pess`, and ∀ε>0, ∀τ ≥
  log(1/(ε(1−γ)))/(1−γ), ‖iter τ − Q⋆‖ ≤ ε with `iter 0 = 0`, sup norm on `S → A → ℝ`. Matches the line-892 claim
  on that domain; trivially fine when ε(1−γ) ≥ 1. Proof via `lem_monotone_contraction_corrected` (X1 ok).
- **R1 (docstring/ledger wording; name).** The docstring says "on γ < 1/2 the unique fixed point Q̂⋆_pe named by
  the claim need not exist uniquely (C10)", and the plan said "the uniqueness clause fails at γ = 0.1 in the C10
  instance". Neither is supported. C10 itself says only that the printed *conjunction* (uniqueness + iterate-order
  clause Q̂_τ ≤ Q̂⋆) is refuted and that "the printed sup-norm rate is not refuted". Critic probe
  `c10_instance.py` (a private Python script in the reviewer's probe folder) reimplements `Input.pess` on the C10 instance
  (γ=0.1, c_b=1, δ=0.5, N=200800): the fixed point is unique (2000 random starts in [0,50]³ all converge to
  Q⋆=(A 0.98469, H 1.11092, L 0)), Q̂₂(A)=0.98622 > Q⋆(A) reproduces C10's order violation, yet
  ‖Q̂_τ − Q⋆‖ ≤ γ^τ/(1−γ) for all τ ≤ 59 and the line-892 count holds for ε ∈ {1,…,1e−8}. So the line-892 claim
  is **not refuted** for γ < 1/2; it is unproved there (the appendix contraction argument needs γ ≥ 1/2).
  Required: replace that docstring sentence with e.g. "restricted to `1/2 ≤ γ`, the domain on which Lemma 6.2 is
  proved (`Lemma6_2_corrected`, C10); for γ < 1/2 the claim is neither proved nor refuted (C10's instance does not
  refute it)". Recommend the suffix `_restricted` (no counterexample to this claim; AGENTS reserves the correction
  framing for source errors) with a `statement-index-scope-disclosures` bullet; if the lead keeps `_corrected` for
  parity with `Lemma6_2_corrected`, the docstring, COVERAGE row and the C10 append must say "inherits the γ ≥ 1/2
  domain of the corrected lemma; not refuted on γ < 1/2", not "fails". Same fix to `iter_iterationCount_corrected`'s
  docstring is optional (it makes no false claim).

## 3. F-items (non-blocking)
- **F1.** DRAFTS §3 "optional observation": `eq:concentrate-infinite` is *not* defined twice in effect — the second
  occurrence (offlineRL.tex:200) is inside `\begin{comment}` … `\end{comment}` (lines 189–229). Drop the observation.
- **F2.** Remark 6.3 (ii) degenerate all-zero-reward witness (see above); disclose in the COVERAGE row ("witness:
  zero rewards, discount 0; C⋆ taken for the library's greedy tie choice") or replace with a unique-optimum witness.
- **F3.** F5 readings for Remarks 6.4/6.5 are acceptable without a suffix (concur with CHECK F5); the COVERAGE rows
  as drafted ("Proved in its formal reading") disclose them adequately.
- **F4.** COVERAGE draft for Lemma line 892: change "Corrected variant proved … Inherits C10" per R1.

## 4. Opinion on the optional named-result ledger entry for Example 6.1
Do **not** add it in this batch. Mathematically it would be justified (the entry is proved as printed and is a
numbered, labeled environment; it is the only `\begin{example}` in the monograph). But
`scripts/progress_dashboard.py:90–110` only matches ledger records against inventory entries of kind
`theorem|lemma|claim`; `docs/source-inventory.json` records `example:offline-bandits` with `"kind": "example"`, so the
record would fail `matched_ids` ("A reviewed result lacks a unique source entry …") and break the dashboard, and the
denominator excludes examples. The drafted record also lacks the `coverage` key that `matched_ids` reads. Adding
examples is a ledger-policy change (numerator/denominator kinds, static gates, site) that the lead should make
deliberately and project-wide; until then record Example 6.1 in COVERAGE.md only.

## 5. Verdicts
| Entry | Verdict |
|---|---|
| Example6_1 | ACCEPT |
| Remark6_5 | ACCEPT WITH DISCLOSURES (F5 reading) |
| Remark6_4 | ACCEPT WITH DISCLOSURES (F5 reading) |
| Eq_defn_Cstar_bandits | ACCEPT |
| Remark6_2 | ACCEPT |
| Remark6_3 | ACCEPT WITH DISCLOSURES (F2) |
| Lemma6_2_iterationCount_corrected | ACCEPT WITH DISCLOSURES, conditional on R1 (docstring/ledger wording; `_restricted` recommended) |

No Lean statement, theorem signature or proof needs to change except the R1 docstring text (and name, if adopted).
Critic artifacts (private, not published): renamed copies of the snapshot, `Probe1.lean` and its output,
`c10_instance.py` and its output; oleans under the project build folder.
