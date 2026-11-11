# CRITIC: integration of corrected Theorem 7.8 and the R5 seed generalisation

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-07): required edits E1 and E2 were applied to C40 in docs/SOURCE-ISSUES.md. The review text below is unchanged.

Reviewer: independent critic subagent (not the builder). Date 2026-11-07. No author approval exists or is
implied. Edited nothing except this report and my probe directory `<reviewer probe folder>/`.

## Verdict

**ACCEPT WITH MINOR EDITS.** The integrated `Thm7_8_corrected` / `Thm7_8_corrected_constSum` (R5 seed form)
are sound, strictly at least as general as the reviewed `Fin K` form (Lean-proved), axiom-clean, and the
index entries are rfl-equal to the library Props with pure-application wrappers. Two wording edits to
`docs/SOURCE-ISSUES.md` C40 are required (E1, E2); E3 is a process note. None affects the mathematics.

## Inputs (sha256)

* `source/upstream/tex/chapters/marl.tex` `8fadfab2c41ecad62349e27478adf2018047ad24a363c63a9918279238d12ffb`
  (same as the first review). `marl.tex:487–503` re-read.
* Integrated files (match BUILD-LOG "integrate" rows and `<builder working folder>/hashes.txt`):
  Defs `0561e2fa7571e1b1…`, Values `7e4c11b816c5486f…`, Hard `9516a2313db3cb85…`, Testing `b9eeeea665967eb7…`,
  HardTesting `9d6a9509d3b9c782…`, Bayes `d5495005a600de27…`, Product `55b91cd2fdf5dfc6…`,
  Statement `c8de2233206e8cb8…`, Main `a4fd0f25a966b0e8…`, `Statements/Ch7.lean` `bf4a98e429134b04…`,
  `Statements/Ch7Proofs.lean` `38b309298b605671…`, `Formalization.lean` `a147c67dd9a72092…`.
  All project oleans are newer than their sources (no stale artifacts).
* Probe `<reviewer probe folder>/Probe.lean` `ac9535d050f65874aa7d14dd535589ba75d9927846bf6bea297baccab5a7b30b`,
  output `Probe.out` `995cc7c9d0fb5c5ce100ef3c038ac84b2c144abdd04ba0ec3959d84b5cc78e2d`.

## Compile evidence

`bash scripts/lean-local.sh <reviewer probe folder>/Probe.lean` (foreground, no `-o`, imports
`Formalization.Statements.Ch7Proofs`): exit 0, ~50 s (one earlier run failed on a typo in my own probe lemma,
fixed; library untouched). Results, all `[propext, Classical.choice, Quot.sound]`:
* `old_of_new : Thm7_8_corrected → OldForm zeroSumAdm` and `old_of_new_constSum` where `OldForm` is the
  reviewed WIP statement with `∀ (K : ℕ) (seed : FiniteDistribution (Fin K)) …, ∃ θ, 1/4 ≤ ∑ ω, seed.prob ω * …`.
  Proof: `μ := seed.prob`, `HasSum` from `hasSum_fintype` + `sum_prob`, then `tsum_fintype`. Also instantiated
  from the index wrappers `Thm7_8_corrected_holds` / `…_constSum_holds` via `example`.
* `seed_avg_summable_mem`: for every game, `ε`, `N`, `Ω`, `μ ≥ 0` with `HasSum μ 1`, and every `rule`, `out`,
  the family `ω ↦ μ ω * P_ω(gap > ε)` is `Summable` and its `tsum ∈ [0,1]`.
* `example : Statements.Ch7.Thm7_8_corrected = Ch7Rest.Marl.Thm7_8_corrected := rfl` and the constSum
  analogue: both succeed.
* `#print axioms` for `exists_param_of_seed_avg`, `hard_family_lower`, both `_holds` wrappers: allowed only.
I did not rerun `IntegrationProbe.lean`; my probe covers its checks (rfl + axioms of the wrappers). Its
recorded output (`<builder working folder>/IntegrationProbe.out`) agrees. Grep of `Marl78*.lean`: no `sorry`, `admit`,
`axiom`, `native_decide`, `set_option`.

## Findings

### (a) R5 seed generalisation

1. **`∑'` is well-behaved.** `exists_param_of_seed_avg` (`Marl78Main.lean:58–96`) proves
   `Summable (fun ω => μ ω * F θ ω)` from `0 ≤ F ≤ 1`, `μ ≥ 0`, `hμ.summable` (`Summable.of_nonneg_of_le`)
   and uses it for `hasSum_sum`. Independently, `seed_avg_summable_mem` shows summability for the exact
   expression in the Prop. Moreover the junk direction is harmless: the conclusion is a *lower* bound
   `1/4 ≤ ∑' …`, and a junk `tsum = 0` would make it false, never vacuously true. `HasSum μ 1` itself implies
   summability of `μ`, so no non-summable seed law is admitted. In ℝ with `μ ≥ 0`, `HasSum` is genuine
   (unconditional) summation and forces countable support, so "countably supported seed law over any type"
   in the docstring is accurate.
2. **One θ for the mixture.** `∃ θ` is outside `∑' ω`; θ is chosen after `Ω, μ, rule, out`, i.e. one
   parameter against the whole randomized learner (`inf_π̂ max_θ`). The proof averages the per-seed Bayes
   bound `hard_bayes` (unchanged) against `μ`, swaps the finite prior sum with the `tsum`, and extracts θ by the
   positive-mass contradiction. Correct.
3. **Generality.** Strictly implies the reviewed `Fin K` form (Lean, finding above). `Ω : Type` (universe 0)
   contains every `Fin K`. D1 is now narrowed to "discrete (countable-support) randomization; measurable
   output kernels not literally quantified", which is how both docstring and C40 now phrase it.
4. **Non-vacuity** is inherited: the first review's `nonvacuous` probe used a point-mass `Fin 1` seed, which
   is an instance of the new binder (via `old_of_new` direction, the new Prop is at least as strong; the
   hypotheses `μ ≥ 0`, `HasSum μ 1` are satisfiable, e.g. `Ω = Unit`, `μ = 1`).

### (b) Docstrings

5. D1–D6 are all present in the `Thm7_8_corrected` docstring (identical in `Marl78Statement.lean` and
   `Statements/Ch7.lean`): size ranges + `not_thm7_8_printed` + prose minimality (D5), zero-sum convention for
   m ≥ 3 and two non-dummy players (D3), `h : ℕ` admissibility (D6), discrete randomization (D1), Markov
   outputs/deviations (D4), `A_j = 0` vacuity (D2). D2 checked: with `Query` empty, `FiniteDistribution Query`
   is empty, and `Ω` must be nonempty since `HasSum μ 1`; so no `rule` exists. Correct.
6. "out sees seed, queries, answers": `out : Ω → (Fin N → Query × Fin S) → JointPolicy`, and
   `interactionLaw` records each entry as `(query, answer)` (`AdaptiveKLDefinitions.lean:72–94`); `rule ω t`
   receives the length-`t` prefix of the same history. Docstring is accurate (R1 addressed).
7. The constSum docstring is accurate (`constSumAdm`: sum 1, all in `[0,1]`).

### (c) Integrated modules vs WIP

8. `diff` of `<builder working folder>/<F>.lean` vs `Formalization/Ch7Rest/Marl78<F>.lean` (the WIP directory is flat;
   there is no `Thm78Wip/` subdirectory): Defs, Values, Hard, Testing, HardTesting, Bayes, Product differ only
   in `import Thm78Wip.X` → `import Formalization.Ch7Rest.Marl78X` and removal of "(WIP)" in the module
   header; their WIP hashes equal the hashes accepted in the first review. Statement and Main differ from
   the current WIP only in imports/header and (Statement) the C40 link text.
9. **Provenance gap (E3).** The current WIP `Statement.lean` (`f4f5b70e…`) and `Main.lean` (`2867c658…`) are
   not the reviewed files (`a24f8cc2…`, `cf7bcf09…`): R5 was applied in place, and the reviewed versions
   are not preserved anywhere under the private working folder. So the "only R5 changed" claim cannot be checked by byte diff.
   I instead re-read all of `Marl78Main.lean` and `Marl78Statement.lean`: the statement bodies differ from
   the reviewed binder description only in the seed binder and `∑'`; `budget_of_N`, the hard-family
   construction, the reward-range proofs (findings 10–13 of the first review) and the `hard_bayes` call are
   as described in the first review; the only new proof content is `exists_param_of_seed_avg` and the
   `Ω, μ` threading in `hard_family_lower`. I accept on this basis.

### (d) Index and wrappers

10. `Statements/Ch7.lean` section `Thm7_8` imports only `Formalization.MultiAgent.LowerBound.Definitions` (definitions; it
    transitively provides `interactionLaw`, `MarkovGame`, `FiniteDistribution`), contains no proofs, writes
    every quantifier and hypothesis out with fully qualified names, and does not refer to another theorem's
    type. rfl-equal to the library Props (probe). Docstrings cite `thm:lower-marl`,
    `chapters/marl.tex:487–503` (correct range) and `docs/SOURCE-ISSUES.md#C40`, and state the differences.
11. `Ch7Proofs.lean`: `Thm7_8_corrected_holds := StatisticalRL.Ch7Rest.Marl.thm7_8_corrected` and the constSum
    analogue: pure application, no restatement. `Formalization.lean` imports all nine `Marl78*` modules and
    the Statements files, so the axiom audit covers them.

### (e) SOURCE-ISSUES C40 "Corrected result"

12. Accurate: module path `Formalization/MultiAgent/LowerBound/Main.lean`, index names, `c₁ = 1/2048`, `c₂ = 2⁻³²`
    (match `Marl78Main.lean`), strict rate, ≥ 1/4, correlated joint outputs, adaptive randomized sampling,
    known shared reward, ranges, the two m ≥ 3 readings, all D-disclosures, "Not author-approved".
13. **E1 (overstatement).** "necessity of S, H, m ≥ 2 is argued in prose only (max A ≥ 2 is machine-checked)".
    What is machine-checked is that the *printed transcription* `Thm7_8_printed` fails at `m = 2, S = H = 1,
    A ≡ 1` (`not_thm7_8_printed`). Removing only `max A ≥ 2` from the corrected Props (keeping `S, H ≥ 2`) is
    not refuted in Lean. Replace with e.g. "(the A ≡ 1 failure of the printed statement is machine-checked,
    at S = H = 1)".
14. **E2 (inaccurate as stated).** "The earlier transcription `Thm7_8_printed` is weaker than the printed
    statement (trivially true once max A ≥ 2)". `Thm7_8_printed` is parameterised by `Adm`; for
    `Adm = sumZeroNormalized` (rewards sum to 0 and lie in `[0,1]`) all rewards vanish, the gap is 0, and the
    core is false for every size, so "trivially true once max A ≥ 2" is false for that reading; the claim is
    also not Lean-checked for any reading. Replace with e.g. "is much weaker than the printed statement
    (data-independent estimators, a claimant-chosen data law, `sup` in place of `max`), so it serves only for
    the A_i = 1 refutation, which remains valid".
15. Minor (optional): C40 describes the zero-sum reading as "rewards summing to 0 with player 1 in [0,1]";
    `zeroSumAdm` also requires all rewards in `[-1,1]` (as the docstrings say). Since it sits under `∃ family`
    this only strengthens the result; adding "and all rewards in [−1,1]" would make C40 match the definition.

## Required edits

* **E1** (C40): restate what is machine-checked about `max A ≥ 2` (finding 13).
* **E2** (C40): drop or qualify "trivially true once max A ≥ 2" (finding 14).
* **E3** (process, non-blocking): in future, snapshot reviewed WIP files before in-place edits (record the
  reviewed `Statement.lean`/`Main.lean` hashes `a24f8cc2…`/`cf7bcf09…` as superseded in BUILD-LOG).
* Optional: finding 15.

No Lean change is required.
