# Five-bin statement audit of the statement index

Date: 2026-11-09/10. Scope: every statement-index entry in `Formalization/Statements/Ch1.lean`–`Ch7.lean` (174 entries at the time of the audit, 179 after the later additions listed below) together with its `_holds` wrapper in `ChNProofs.lean`.

## Method

The audit follows the `lean-statement-audit` skill (`skills/lean/skills/lean-statement-audit/SKILL.md`), adapted because this project has **no author-approved frozen declarations** (none may be invented; see `AGENTS.md`):

- The audit target is the statement-index `Prop` and its wrapper, not a frozen manifest entry.
- Each auditor first reconstructed the printed statement from the pinned `.tex` source (premises, quantifier order, conclusion, constant scope), and only then compared it with the Lean `Prop`.
- Every binder and hypothesis, with project-owned definitions and bundles expanded, was put in exactly one bin:
  - **SOURCE**: an explicit premise of the printed statement;
  - **STANDING**: a standing assumption of the chapter, with line citation;
  - **TYPING**: pure type formation;
  - **DISCLOSED**: a deviation named by the `_corrected`/`_restricted` suffix, stated in the docstring, and recorded in [SOURCE-ISSUES.md](../SOURCE-ISSUES.md). This bin replaces the skill's author-ruled bin, because there are no author rulings: disclosed is never "approved";
  - **EXCESS**: anything else. Any EXCESS fails the entry, as does any deviation in an unsuffixed entry.
- Auditors also checked quantifier order and constant scope, conclusion carriers and exponents, junk values, satisfiability of hypotheses, and that each wrapper only applies existing library theorems.
- Eight auditors, each independent of the entries' builders, covered the eight batches below. A separate builder fixed the failures, and the original auditors re-audited each fix.

## Results

| Batch | Entries | PASS | PASS-DISCLOSED | FAIL (first pass) | FAIL after fixes |
|---|---|---|---|---|---|
| [Ch1–Ch2](ch1-ch2.md) | 28 | 28 | 0 | 1 | 0 |
| [Ch3](ch3.md) | 19 | 11 | 8 | 1 | 0 |
| [Ch4](ch4.md) | 25 | 20 | 5 | 0 | 0 |
| [Ch5, part A](ch5a.md) | 18 | 4 | 14 | 0 | 0 |
| [Ch5, part B](ch5b.md) | 19 | 6 | 13 | 0 | 0 |
| [Ch6](ch6.md) | 26 | 12 | 14 | 1 | 0 |
| [Ch7, part A](ch7a.md) | 20 | 2 | 18 | 1 | 0 |
| [Ch7, part B](ch7b.md) | 19 | 4 | 15 | 3 | 0 |
| **Total** | **174** | **87** | **87** | **7** | **0** |
| [Later additions, Ch7](../critic-confregion.md) ([and](../critic-confcalib.md), [and](../critic-chisq.md)) | 6 | 0 | 6 | 0 | 0 |
| **Total now** | **180** | **87** | **93** | **7** | **0** |

The PASS and PASS-DISCLOSED columns are the verdicts after re-audit. The later additions (2026-11-10) are the oracle-covariance confidence-region entries `Eq_convex_Cdelta_{fixedShape,ellipsoid,rectangle}_corrected_oracle` `Eq_convex_Cdelta_{ellipsoid,rectangle}_corrected_oracle_calibrated` and `Eq_convex_Cdelta_ellipsoid_corrected_oracle_chiSquared`; each was five-bin audited by its independent reviewer.

## First-pass failures and their fixes

No failure was a mathematical error in a proof. Each was either a statement entry that assumed more than the printed result, or an entry that narrowed the printed claim while carrying a plain name.

- **Lemma 2.9 (Freedman).** The conditional-variance bound was assumed pointwise for a fixed version of the conditional expectation. It is now almost sure, matching the printed reading.
- **Theorem 3.9, minimax lower bound.** Renamed `Thm3_9_minimaxLowerBound_restricted`. The seed space is now any type, removing a universe-0 limit.
- **Lemma 6.11.** The entry no longer fixes one tie choice for π⋆. It now quantifies over every Q⋆-greedy deterministic π⋆.
- **Theorem 7.10.** Renamed `Thm7_10_restricted`, because the printed algorithm class allows any distributed mean-estimation routine (federated chapter, line 196), while only exact averaging is modelled ([C42](../SOURCE-ISSUES.md#C42)). The named-result split moved from 45/30/15 to **44/30/16** (printed/corrected/restricted).
- **Robust-RL displays** (`Eq_mdp_value_Q`, `Eq_bellman_equ_infinite_all`, `Eq_robust_bellman_fixedPoint`). Now `_restricted`, and generalized from the TV and χ² balls to every uncertainty set whose infimum is attained. That is the disclosed reading of the printed "distance-like ρ".

Smaller improvements made during the audit:

- `Lemma5_18_restricted` now holds for every c_b ≥ 2.
- Docstrings now cite the standing assumptions they rely on.
- New scope notes in SOURCE-ISSUES: γ > 0, the bounded start of value iteration, Remark 4.5(iii) holding only for t ≥ τ̂, and deterministic estimators in C7 and C38.

## Limits of this audit

- It is a reading audit of statements. It does not re-check library proofs, which the Lean kernel checks, with the axiom audit allowing only `propext`, `Classical.choice` and `Quot.sound`.
- Some deep definitions were checked only at signature and docstring level. The batch reports say where.
- The statement files `Statements/Ch2.lean`, `Ch4.lean` and `Ch6.lean` import some modules that also contain theorems. The static-gate allowlist permits these imports but does not justify them one by one.
- Nothing here is author-approved.
