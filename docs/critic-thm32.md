# Critic report: printed entries `Thm3_2`, `Lemma3_5` (2026-11-10)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of the printed statement-index entries `Thm3_2` (Theorem 3.2, `Thm:sample-compl-main`) and `Lemma3_5` (Lemma 3.5, `lem:policy-learning-evaluation`) in `Formalization/Statements/Ch3.lean`, with their `_holds` wrappers in `Formalization/Statements/Ch3Proofs.lean`.

Integration note: verdict ACCEPT; section 5 applied on 2026-11-10. The named-result ledger records for Theorem 3.2 and Lemma 3.5 now point at `Thm3_2`/`Lemma3_5` (status: proved as printed; `correction_status` dropped, since no correction or restriction remains); `Thm3_2_positiveN` and `Lemma3_5_positiveN` are kept as supporting entries with reader notes; the SOURCE-ISSUES scope-disclosure bullet, the COVERAGE rows (including the three `Implied by` rows that cited `Thm3_2_positiveN`), Deviation 1 in ERRATA-AND-DEVIATIONS and `docs/statement-audit/ch3.md` (§4, §7 and an addendum: `hN` bin DISCLOSED → TYPING) were updated. The `_positiveN` docstrings were not changed. No Lean change.

Independent critic (did not build). Read-only except this report and one local probe (`<local probe>` = a copy of
`Ch3Proofs.lean` with two `#print axioms`).

Verdict: **ACCEPT** (both entries PASS). Doc/ledger follow-ups listed in section 5 are required in the
same change that moves the ledger, but no Lean change is needed.

## 1. Independent reconstruction and the N = 0 question

### Theorem 3.2 (`Thm:sample-compl-main`, `chapters/generative_model_model_based.tex:900–923`; algorithm 814–865)
∃ universal c₀ > 0 such that for any (finite) MDP, any 0<δ<1, any 0<ε≤1/(1−γ), if
N ≥ c₀ log(SAN/((1−γ)²εδ))/((1−γ)³ε²), then with probability ≥ 1−δ every optimal deterministic policy π̂⋆
of the empirical MDP M̂ satisfies V^{π̂⋆}(s) ≥ V⋆(s) − ε ∀s and Q^{π̂⋆}(s,a) ≥ Q⋆(s,a) − γε ∀(s,a).

### Lemma 3.5 (`lem:policy-learning-evaluation`, same file 1306–1326)
For 0<δ<1, β₁ = 2 log(16SAN/((1−γ)δ)); with c₀, c₁ "sufficiently large universal constants", if
N ≥ c₀β₁/(1−γ) then w.p. ≥ 1−δ: ‖V̂^{π̂⋆} − V^{π̂⋆}‖∞ ≤ c₁√(2β₁/(N(1−γ)³)) and
0 ≤ V⋆ − V^{π̂⋆} ≤ 2c₁√(β₁/(N(1−γ)³))·1 (simultaneously).
"Sufficiently large" vs ∃: both constants act monotonically (larger c₀ strengthens the premise, larger c₁
weakens the conclusion), so ∃c₀,c₁ is equivalent to ∀ c₀,c₁ above thresholds. ∃ is faithful.

### Is N = 0 genuinely outside the printed domain?
Yes, not merely awkward:
- `DiscountedMDP` forces S, A ≥ 1 (`state_nonempty`, `action_nonempty`, MDP/CoreDefinitions.lean:31–32), so
  SAN = 0 exactly when N = 0, and both thresholds contain log 0 (undefined over ℝ). Lemma 3.5's bounds also
  divide by N.
- The algorithm's empirical kernel `eq:defn-empirical-P` (:826–830) is (1/N)Σ_{i=1}^N 1{…} = 0/0 at N = 0, so
  M̂, V̂^π and π̂⋆ do not exist. No convention makes the N = 0 instance a meaningful claim (any junk P̂ would
  make it false for small δ, not trivially true).
- Is the guard redundant in Lean? No. With Lean's log 0 = 0 the premise reads c₀·0/(…) = 0 ≤ 0, which holds at
  N = 0 for every admissible parameter set. So the printed premise does not exclude N = 0 in Lean; a typing
  witness is needed. (Contrast Thm3_9, whose threshold has no N in the log and is defined at N = 0.)
- "Event = whole space at N = 0": the N = 0 instance then says 1−δ ≤ P(Ω) = 1, true and content-free. This
  claims nothing the print does not claim (the print claims nothing at N = 0). For N > 0, by proof
  irrelevance {data | ∀ hN, E hN data} = {data | E hN₀ data}, so `Thm3_2 ↔ Thm3_2_positiveN` and
  `Lemma3_5 ↔ Lemma3_5_positiveN` with the same constants (N = 0 direction uses that `samplingLaw M 0` is a
  probability measure; the wrapper uses `probReal_univ`, which compiled). No content is lost or added.
- Consistency with precedents and with the project's positivity-guard rule from the external-review triage ("TYPING when the printed statement is undefined, or
  trivially true under the source's own convention, on the excluded domain; DISCLOSED only when it makes a
  meaningful non-trivial claim there"): Lemma3_4 (hN TYPING, ε = 1/(N(1−γ))), Lemma3_6 (hN TYPING),
  Thm3_9 (witness inside the event), Eq_lemma_VarP_V_bound (0<γ domain). Thm 3.2/Lemma 3.5 fall in the
  "undefined" branch, so TYPING is correct and the unsuffixed name is right.

## 2. Five-bin audit

### `Thm3_2` — Formalization/Statements/Ch3.lean:127 (docstring 106–126)
| binder | Lean type | bin | citation |
|---|---|---|---|
| c₀ (∃, before all) | ℝ, 0 < c₀ | SOURCE | :902 "universal constant c₀>0" |
| State, Action, Fintype | Type*, instances | TYPING | finite S, A (chapter standing) |
| M | DiscountedMDP (nonempty S, A; r∈[0,1]; 0≤γ<1) | STANDING | chapter MDP setting |
| N | ℕ | SOURCE | sample size per pair |
| δ, 0<δ, δ<1 | ℝ | SOURCE | :902 |
| ε, 0<ε, ε≤1/(1−γ) | ℝ | SOURCE | :902 |
| threshold `c₀ log(SAN/((1−γ)²εδ))/((1−γ)³ε²) ≤ N` | Prop | SOURCE | `EqnSamples-main` :917–920 |
| hN : 0<N (inside event) | Prop witness | TYPING | P̂ = counts/N, log(SAN) (:826–830, :919) |
| f, EmpiricallyOptimal (∀ stationary π, V̂^π ≤ V̂^f pointwise) | inside event | SOURCE | "any optimal deterministic policy" :902, `defn:pi-p-star-noperturb` |
Conclusion: V⋆(s)−ε ≤ V^f(s) ∀s; Q⋆(s,a)−γε ≤ Q^f(s,a) ∀(s,a); P ≥ 1−δ. Matches :905–911.
Counts: SOURCE 7, STANDING 1, TYPING 2, DISCLOSED 0, EXCESS 0. Self-contained, no junk (log 0 only at N=0,
where the event is Ω). **PASS.**

### `Lemma3_5` — Ch3.lean:223 (docstring 207–222)
| binder | Lean type | bin | citation |
|---|---|---|---|
| c₀, c₁ (∃, before all), >0 | ℝ | SOURCE | :1324 (monotone, see §1) |
| State, Action, Fintype | | TYPING | |
| M | DiscountedMDP | STANDING | |
| N | ℕ | SOURCE | |
| δ, 0<δ<1 | ℝ | SOURCE | :1310 |
| `c₀·leaveOneOutBeta/(1−γ) ≤ N`, `leaveOneOutBeta = 2 log(16SAN/((1−γ)δ))` (Ch3Definitions.lean:202) | Prop | SOURCE | :1311–1314, :1324 |
| hN inside event | witness | TYPING | as above |
| f, EmpiricallyOptimal | inside event | SOURCE | π̂⋆ |
Conclusion: sup-norm bound c₁√(2β₁/(N(1−γ)³)) and pointwise 0 ≤ V⋆−V^f ≤ 2c₁√(β₁/(N(1−γ)³)), jointly, on
one event. Matches :1317–1322. Counts: SOURCE 7, STANDING 1, TYPING 2, EXCESS 0. **PASS.**

## 3. Wrappers (Ch3Proofs.lean:41–51, 73–85)
Each obtains the constants from the existing exports
(`mainSample_policyLearning_universal_constant`, `source_policyLearning_pointwise_universal_constants`),
splits N = 0 (`probReal_univ` + `measureReal_mono` with absurd witness) / N > 0 (export + monotonicity,
dropping the export's extra conjunct for 3.5). No restated or second proof. OK.

## 4. Compilation and axioms (run by this critic)
- `bash scripts/lean-local.sh Formalization/Statements/Ch3.lean`: exit 0 (only pre-existing unused-variable
  warnings at :267).
- `bash scripts/lean-local.sh Formalization/Statements/Ch3Proofs.lean`: 0 errors.
- `<local probe>`: `Thm3_2_holds` and `Lemma3_5_holds` depend on axioms
  [propext, Classical.choice, Quot.sound].
Not run: full `lake build`, `Audit.lean`, `scripts/check.py`, static gates.

## 5. Recommended ledger/doc change (same change)
`docs/named-result-status.json`, `certified_named_results`:
- Theorem 3.2: `lean_statement` → `StatisticalRL.Statements.Ch3.Thm3_2`, `lean_statement_proof` →
  `…Thm3_2_holds`; add `docs/CRITIC-…` evidence (this report, if published as a doc) to
  `supporting_evidence`; `statement_scope` →
  "printed; for every deterministic policy optimal for the empirical MDP (no tie rule fixed). The empirical
  model is typed by a `0 < N` witness inside the event: at N = 0 the printed threshold (log of SAN = 0) and
  the empirical model (0/0) are undefined, so that case is outside the printed domain and the event is the
  whole sample space. A universal constant exists (the proof gives 10240)."
  `display_note` → "Proved as printed. There is a universal constant (the proof gives 10240)."
  Remove `correction_status` (no correction/restriction remains; proof_origin stays source-proof), unless
  `correction_status` is required for the 10240-gap repair elsewhere — check C-entries before dropping.
- Lemma 3.5: same pattern; `statement_scope` → "printed; for every empirically optimal deterministic policy
  (no tie rule fixed). `0 < N` witness inside the event: at N = 0, β₁ = 2 log(16SAN/((1−γ)δ)) has SAN = 0,
  both bounds divide by N and P̂ is 0/0, so N = 0 is outside the printed domain. Universal constants exist
  (explicit in the proof)."; `display_note` → "Proved as printed. There are universal constants (explicit
  in the proof)."
Also: reword `docs/SOURCE-ISSUES.md:587–591` (no longer a scope disclosure: "indexed in printed form as
`Thm3_2`/`Lemma3_5` with the `0 < N` witness inside the event (domain of definition, as for Thm3_9);
`Thm3_2_positiveN`/`Lemma3_5_positiveN` retained"), keep the approxPlanner sentence (that entry is still
restricted; the same argument would apply to it but is not part of this review); update COVERAGE.md rows and
`docs/statement-audit/ch3.md` §4/§7 bins (DISCLOSED → TYPING); move `Thm3_2_positiveN`/`Lemma3_5_positiveN`
to `entry_display_notes` as supporting entries if the site requires a note for unrecorded entries; optionally
reword their docstrings from "Restricted …" to "Positive-N form; the printed form is `Thm3_2`".
