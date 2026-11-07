# Follow-up critic report: corrections for C22 and the Lemma 6.11 disclosure

Public copy of the independent critic report; local paths removed.

- Date (UTC): Fri Nov  6 20:01:19 UTC 2026 (from `date -u` at review start)
- Reviewer: independent Claude critic subagent (did not write the reviewed text)
- Git HEAD: `6bac672b2956953c2587c9785cda8de7a5b6eb72`, branch `batch-ch2-ch3-ch6-20261106`. The reviewed texts are uncommitted working-tree changes.
- Mode: source-only; no Lean run (no lake, `check.py`, `lean-local.sh` or LSP).
- Previous report: the private original of `docs/critic-c22-lemma6-11-disclosure.md`, SHA-256 of the original `ea17363ae8f663aefc2f753cdf5083eb2f72dfb160db2c20b63f47d49ab34916`. It was not modified.

## 1. Files read (SHA-256)

| File | SHA-256 | Lines used |
|---|---|---|
| `source/upstream/tex/chapters/offlineRL.tex` | `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4` (matches pin) | 1754–1772, 2284–2300, 4674–4800 (other uses of κ) |
| `docs/SOURCE-ISSUES.md` | `52520d8661da5ef25a74e8fc2fc5d62e5167396b77104c24403fedee05cdf0bd` | 387–405, 756–807 |
| `Formalization/Statements/Ch6.lean` | `691ac91c8fcbee138b0b5b7d43a45bb1cffcfadf1ce7503dfc03fc5d5ce99684` | 186–213 |
| `Formalization/Statements/Ch6Proofs.lean` | `d80a704b5693f0181a8b6f2df3c9bd3169eadfc87506392e51995b169b147542` | unchanged since the first report |
| `Formalization/OfflineRL/LCBQUsefulSeries.lean` | `e3a0f9d9a0efe6ee6caeacf725bd74d237bcfde3d8ac347b352cb9a74bda8d35` | 1–24, 54–67 |
| `docs/COVERAGE.md` | `4c9019652eed9c2b0df206efc66d7fbef3115b5cb0707ac0f1e037e5d4d73cf3` | row 92 |
| `docs/PROGRESS.md` | `b5376c213708151a86146ca6b9fd5476fff202e1a85cbbf5b190e42d17dbe2a4` | 11–13, unchanged |
| scratch `c22_corner.py`, outside the project | `1cbbc0f90d56505a9df3a2b7ac9d31e2ad1ba4c401e7021a2b49a56770bcef9c` | randomized check of the corner |

The full scratch path is (local scratch path omitted).

**Checks that the corrections are docstring-only:**
- In `Ch6.lean`, the body of `Lemma6_11_restricted` (199–211) is identical to the body reviewed before. Only the docstring grew, by one line.
- In `LCBQUsefulSeries.lean`, the signature of `lcbq_useful` (55–66) is unchanged, with literal constant 84. The file grew from 249 to 251 lines, which matches the two added docstring lines.

## 2. Line-by-line check of the Theorem 6.8 corner argument (C22, SOURCE-ISSUES:794–801)

Theorem 6.8's hypotheses, from `offlineRL.tex:1756–1771`:
- 0<δ<1;
- ε ∈ (0, 1/(1−γ)];
- C⋆ ≥ 1;
- T ≥ c₂ S C⋆ log(SAT/((1−γ)δ)) / ((1−γ)⁵ε²);
- c₂ is a "large enough" universal constant;
- γ ∈ [0,1).

| Step in the text | Check | Status |
|---|---|---|
| "In the corner δ > SAT/e we have SAT ≤ 2, so T ≤ 2" | SAT < eδ < e and SAT ∈ ℕ give SAT ≤ 2. With S, A ≥ 1 this gives T ≤ 2. | correct |
| "with ε ≤ 1/(1−γ), S, C⋆ ≥ 1 and log(SAT/((1−γ)δ)) ≥ log(1/(1−γ)) ≥ γ, the condition gives γ ≤ T/c₂ ≤ 2/c₂" | From ε² ≤ (1−γ)^{−2}, the bound (1−γ)⁵ε² ≤ (1−γ)³ ≤ 1 follows. SAT/δ > 1 gives the first log inequality, and −log(1−γ) ≥ γ gives the second. So T ≥ c₂γ. | correct |
| "For c₂ ≥ 32 this makes κ ≤ 8γ ≤ 1/2" | H ≥ 1 because log(SAT/δ) > 0, so (1+1/H)³ ≤ 8. Then 8γ ≤ 16/c₂ ≤ 1/2. | correct |
| "since δ/(ST⁴) > A/(eT³) ≥ 1/(8e)" | δ > SAT/e gives δ/(ST⁴) > A/(eT³). With A ≥ 1 and T ≤ 2 this is ≥ 1/(8e). | correct |
| "the lemma's conclusion holds there with a constant below 84" | See the constant discussion below. Both derivations give a constant well below 84. | correct |
| "So κ < 1 holds on all of Theorem 6.8's hypotheses, and the theorem is unaffected." | Outside the corner, log(SAT/δ) ≥ 1 gives κ < 1. Inside it, κ ≤ 1/2 for c₂ ≥ 32. In the proof of Theorem 6.8, κ is used only through κ < 1 (`:4795`, for α = 0) and through Lemma 6.11. Both are therefore available. The qualifier "for c₂ ≥ 32" is implicit, carried over from the previous sentence (N2). | correct |

**8e versus 16e.** Put A₁ = ⟨d,W⟩/(1−γ) and A₂ = δ‖W‖/(ST⁴(1−γ)). In the corner, ‖W‖ < 8e·A₂. Both bounds below are valid; neither is wrong.

- **16e:** bound the whole series, including j = 0, by Σ_j κ^j ‖W‖ ≤ 2‖W‖ < 16e·A₂. This gives the constant 16e ≈ 43.5.
- **8e (the tighter bound):** keep the j = 0 term separate.
  - First, ρᵀW ≤ A₁, because d ≥ (1−γ)ρ entrywise and W ≥ 0.
  - Then the left side is at most ρᵀW + κ/(1−κ)·‖W‖ ≤ A₁ + ‖W‖ < A₁ + 8e·A₂ ≤ 8e(A₁+A₂).
  - This gives the constant 8e ≈ 21.7.

The text says only "a constant below 84", which is true under either derivation.

**Randomized check.** I sampled random S- and A-state chains with SAT ≤ 2, δ ∈ (SAT/e, 1), γ ∈ [0, 0.07] and c₂ = 32, keeping only tuples that satisfy Theorem 6.8's condition.
- 290 feasible samples were found.
- The maximum of LHS/(A₁+A₂) was 0.611, far below both 8e and 16e.

**Side observation.** For c₂ ≥ 32 the corner is in fact only S=A=T=1. The reason: SAT = 2 would need log(2/δ) ≤ T/c₂ ≤ 1/16, i.e. δ ≥ 2e^{−1/16} > 1. The text's bound T ≤ 2 remains valid, merely not tight (N4).

## 3. Status of the earlier findings

**F1 (MAJOR, the corner left open): RESOLVED in C22.**
- The argument is now present and correct (section 2).
- "This is not a counterexample to Theorem 6.8" is stated, following the C19 precedent.
- "Open (formal coverage only)" correctly narrows the open item.
- The scope-disclosure item points to C22 "for the source error and why Theorem 6.8 is unaffected".
- The short echoes in COVERAGE and `Ch6.lean` introduced a new imprecision; see N1.

**F2 (MINOR, title): RESOLVED.**
- The new title is "fails when log(SAT/δ) is small".
- The added sentence "failures need SAT ≤ 2, since SAT ≥ 3 gives log(SAT/δ) > 1 for every δ < 1" is correct: SAT/δ > 3 > e.

**F3 (MINOR, header inconsistency): RESOLVED.**
- The header now adds: "Where an item links to a source-issue candidate, that candidate records the asserted error."
- The Lemma 6.11 item no longer asserts the error itself; it defers to C22.

**F4 (NOTE, attribution of the constant 84): RESOLVED in C22.**
- C22 now reads "states the lemma with this premise and an existential universal constant; its proof supplies C = 84".
- The scope item still says "(constant 84)", and COVERAGE still says "explicit universal constant 84". Both are acceptable, because the library export `lcbq_useful` carries 84 literally.

**F5 (NOTE, the Ch6 docstring tied falsity only to κ ≥ 1): RESOLVED.** The docstring now says "κ < 1 can fail, and even with κ < 1 no universal constant works when log(SAT/δ) is small".

**F6 (NOTE, weak "so" inference; γ=0 example): RESOLVED.** The "only bounds T from below, so" wording is gone, and the example is now followed by the corner argument.

**F7 (NOTE, locators): RESOLVED.**
- C22 now cites κ at lines 2284–2289, which is correct.
- C22 now states "0 < η < 1/8" and "(with the normalised occupancy d_ρ^⋆)".
- H is still cited as 1667–1672, which is acceptable.
- The Ch6 docstring still gives no line range for κ; that is acceptable.

**F8 (NOTE, optional sharper threshold): NOT ADOPTED.** No action was needed.

**F9 (NOTE, overlong line in `LCBQUsefulSeries.lean`): RESOLVED.** The module docstring is now three paragraphs, and the joined line is gone.

**C21 note: RESOLVED.**
- `<a id="C21"></a>` was added at line 758.
- The optional numeric remark was not added; that is acceptable.
- The C21 text and locator are unchanged and remain correct.

## 4. New findings

**N1 — MINOR. Two summaries justify "Theorem 6.8 is unaffected" by κ < 1 alone, which the same texts say is insufficient.**
- Where:
  - COVERAGE row 92: "Theorem 6.8 is unaffected because its own hypotheses give κ<1".
  - `Ch6.lean:195–196`: "they do give `κ < 1` in the remaining corner `δ > SAT/e`, so that theorem is unaffected".
- The problem:
  - `Ch6.lean:193–194` itself says "even with κ < 1 no universal constant works". C22's η-family has κ = 1 − 8η < 1, and the lemma still fails.
  - So "κ < 1, hence unaffected" is a non-sequitur.
  - The actual reason (C22:797–800) is that in the corner, with c₂ ≥ 32, κ ≤ 1/2 and δ/(ST⁴) > 1/(8e). Together these give the lemma's conclusion.
- The conclusion "unaffected" is true; only the stated reason is wrong.
- Correction for COVERAGE: "Theorem 6.8 is unaffected because, with c₂ ≥ 32, its own hypotheses force κ ≤ 1/2 and δ/(ST⁴) > 1/(8e) in that corner, which gives the lemma's conclusion; …". Make the same change in `Ch6.lean`.
- `LCBQUsefulSeries.lean:15–16` says only "that theorem's hypotheses still give κ < 1 in the corner …, but this result does not cover that corner". That is true and claims no consequence, so it needs no fix (but see N2).

**N2 — NOTE. The c₂ qualifier is implicit in three places.**
- C22:801 ("So κ < 1 holds on all of Theorem 6.8's hypotheses"), `Ch6.lean:195–196` and `LCBQUsefulSeries.lean:15–16` rely on c₂ being large.
- The bound needs c₂ ≥ 32 as argued; c₂ > 16 already suffices for κ < 1.
- Theorem 6.8 allows any sufficiently large c₂, so the statements are true. Writing "(for c₂ ≥ 32)" would make them self-contained.

**N3 — NOTE.**
- C22:796 says "holds for every δ ≥ e^{−1/c₂}, where log(SAT/δ) < 1". This needs c₂ > 1 and δ < 1; at c₂ = 1 and δ = e^{−1}, log(SAT/δ) = 1.
- This is harmless, since c₂ is large and δ < 1 is standing.

**N4 — NOTE (optional).** For c₂ ≥ 32 the corner contains only S=A=T=1 (section 2). The text's "T ≤ 2" remains a valid, non-tight bound.

## 5. Verdict

VERDICT: ACCURATE-WITH-FINDINGS — F1–F7, F9 and the C21 note are resolved and the new Theorem 6.8 corner argument in C22 is correct line by line (its "constant below 84" holds; 8e is the tighter valid constant, 16e is also valid), but the COVERAGE row and the `Ch6.lean` docstring justify "Theorem 6.8 is unaffected" by `κ < 1` alone, which the texts themselves say does not suffice (new MINOR N1).
