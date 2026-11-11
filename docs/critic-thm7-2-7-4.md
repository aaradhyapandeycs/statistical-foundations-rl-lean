# CRITIC: corrected Theorems 7.2 (TV) and 7.4 (χ²), DRVI upper bounds — Lean WIP review

Public copy of the independent critic report; local paths removed.

Independent critic; I am not the builder. I edited no project file. My only writes are this report and
`<reviewer probe folder>/` (`NonVacuity.lean`, `nonvacuity.out`, `recompile.log`).

## Verdicts

| Theorem | Verdict |
| --- | --- |
| `Ch7.Thm7_2_corrected` / `DRVI.thm7_2_corrected_holds` | **ACCEPT** (statement faithful up to the C37 count only; proof compiles from source; standard axioms; non-vacuous) |
| `Ch7.Thm7_4_corrected` / `DRVI.thm7_4_corrected_holds` | **ACCEPT** (same; the A = 1 case is genuinely proved inside the proof, no added hypothesis) |

No blocking findings. The findings below are informational or concern integration only.

## Pins

| Item | sha256 |
| --- | --- |
| Repo HEAD | `73929ac3f43f9d3f2ced60d709b0dd04903c167d` |
| `source/upstream/tex/chapters/robust_RL.tex` | `95ce19a9bcdb275c9d4c04e4b20e836c8e5f0965426e955999817e82141196d9` |
| `Formalization/RobustRL/LowerBounds/Ch7Definitions.lean` | `ff3f0c13732dcbff34aa8734fee89e9d42bdbbd5fd4e5dd842acd5d698a3ea82` |
| `Formalization/RobustRL/LowerBounds/Ch7PrintedStatements.lean` | `d04bb084e64e6590c696a8ab33492f74976a51dde29f9c587a0af680d1b3deb6` |
| `<builder working folder>/Thm72Wip/Statement.lean` | `5ab18c75525ec3d93c663dbc7479e345fb33cfee730faa381d161d5f203c0ffc` |
| `<builder working folder>/Thm72Wip/Thm72Main.lean` | `6aa9feeed8f28cb5cfd05017affaee30a9d6f194715bfd48cb89040b3b5be050` |
| `<builder working folder>/Thm72Wip/Thm74Main.lean` | `7a2d8f11f1611f0fed3c56f871da95a195f39f0ea97a630f91a1015fb7e80fab` |
| `<builder working folder>/DiffProbe.lean` | `cd4f935421a3bc4427f8d92bbc826a84a247b953114f6c25032192132226a1df` |
| `<builder working folder>/AxiomProbe.lean` | `3783909588bbea1702d50e7a15ffb0d44148bf4be916935b8c4b4811f3e18f80` |
| `<reviewer probe folder>/NonVacuity.lean` (mine) | `1bf8f31b1f5b4ef218e6b452e0758b83179ae082e8780ad3028489bf05cbf4f7` |

`diff -r Thm72Wip Thm72Wip.reviewed-snapshot` is empty, so the reviewed snapshot equals the live WIP. The other 20
module hashes are listed in the appendix.

## 1. Source reconstruction (done before reading the Lean)

- **Model** (`robust_RL.tex:19–157`). The uncertainty set is (s,a)-rectangular. V^{π,σ} is the inf over admissible
  kernels of the actual value (`:76–79`). V^{⋆,σ} = max_π V^{π,σ} (`:94–96`). Samples are N i.i.d. draws per (s,a)
  from P^0 (`:135–147`).
- **DRVI** (`:206–289`). It runs on the empirical kernel from Q̂_0 = 0 with the exact inner infimum and outputs a
  greedy π̂ with unspecified ties.
- **Lemma 7.1** (`:302–324`) is the strong duality for the inner infimum.
- **Thm 7.2** (`:342–359`). There exist C1, C2 > 0. Hypotheses: γ ∈ [1/4,1), σ ∈ (0,1), δ ∈ (0,1),
  ε ∈ (0, √(1/max{1−γ,σ})], T = C1 log(N/(1−γ)), and N ≥ C2 log(SAN/((1−γ)δ)) / ((1−γ)² max{1−γ,σ} ε²).
  Conclusion: with probability ≥ 1−δ, V⋆ − V^{π̂} ≤ ε at every state.
- **Thm 7.4** (`:437–450`). The same, with χ², σ ∈ (0,∞), ε ∈ (0, 1/(1−γ)],
  N ≥ c2 (1 + max{√σ,σ}/(1−γ)) log(SAN/δ) / ((1−γ)³ε²), and T = c1 log(N/(1−γ)).
- **Divergences:** TV at `intro.tex:223`, χ² (with P ≪ Q) at `intro.tex:228–234`.
- **C37** replaces the count with T ≥ C1 log(N/(1−γ))/(1−γ).

## 2. Statement audit (check 1)

**Mechanical diff, done three ways:**
- **(a) My own textual diff.** I wrote a Python `difflib` comparison of the `def` bodies in
  `Ch7PrintedStatements.lean` against those in `Statement.lean`. The only hunks are:
  - the name, and the dropped `roundT` parameter;
  - one inserted line, `∀ T : ℕ, C₁ * Real.log (N / (1 - M.discount)) / (1 - M.discount) ≤ T →` (c₁ for 7.4);
  - the DRVI argument `roundT (C₁ * Real.log (N / (1 - M.discount)))` replaced by `T`.

  Every other line is byte-identical: the ∃-constants prefix, the `Type` universe binders, all ranges, `hN`, the
  sample-size formula, `∀ pick` with greedy-for-every-data, and the event under `samplingLaw M N`.
- **(b) DiffProbe re-elaborated by me** (exit 0). The corrected Prop is the template by `rfl`, and the printed Prop
  is equivalent (`↔`) to the template with `IterOK := (T = roundT(C₁ log(N/(1−γ))))`. The template has the same
  quantifier order as the printed statement, with T inserted after the sample condition and before `pick`. T is
  data-independent, as in the source.
- **(c) Strength.** "∀ T ≥ threshold" is the strongest reading. It implies the conclusion for every rounding of the
  corrected formula and for every larger T. It is not weaker than printed in any other respect.

**Further checks:**
- **Constants** are quantified before `State`, `Action`, `M` and the rest, matching `:358`/`:449`.
- **Universal greedy picks** are kept: no tie rule is chosen.
- **The event** is `{data | ∀ s, V⋆ − V^{detPolicy(pick data)} ≤ ε}` under the real product law
  `ModelBasedPolicyLearning.samplingLaw M N`, which is `Measure.pi` of the true rows (`Ch3Definitions.lean:69–71`).
- **The sample-size formulas are verbatim.**
- **Junk-value check on the logs.** S, A, N ≥ 1, 1−γ ≤ 3/4 and δ < 1 make every log argument > 1, so no
  log-of-nonpositive junk can make the N-condition easier. The one junk case, N = 0 where `log 0 = 0`, is excluded by
  `hN`, which the printed transcription already carries. At N = 0 the empirical kernel is undefined, so `hN` is not a
  smuggled hypothesis.

## 3. Definitions and the new library facts (check 2)

The statement uses only the accepted `robustPolicyValue`, `robustOptimalValue`, `tvBall`, `chiBall` (= `qChiBall`),
`empiricalDRVI`, `IsGreedy`, `detPolicy` and `samplingLaw`. `grep` finds no def, instance or notation in the WIP
shadowing them; the only WIP defs are proof-internal helpers. A probe `example : Ch7.Thm7_2_corrected :=
DRVI.thm7_2_corrected_holds` elaborates, and likewise for 7.4.

- **R0b** (`PolicyEvaluation.lean:229–259`, `familyRobustValue_eq_policyFix`) is genuine and not circular.
  - `policyFix` is the unique fixed point of the robust policy operator, built from the ShiftBound contraction
    (`Analysis.contraction_exists_unique`), not from the robust value.
  - The proof uses `IsLeast.csInf_eq`. The worst kernel of the fixed point lies in the set, and its actual
    trajectory value equals `policyFix` through the library `trajectoryExpectedValue_eq_valueFixedPoint` and
    `valueFixedPoint_characterization`. Every admissible kernel's actual value is a super-solution, hence ≥
    `policyFix`.
  - So the sInf is attained, and the junk value `sInf ∅ = 0` cannot occur.
- **R0d** (`Optimality.lean:154–181`) is genuine. It uses `IsGreatest.csSup_eq` over stationary randomized policies.
  `detPolicy (optPolicy …)` attains `optFix`, and every π has `policyFix ≤ optFix` (`policyFix_le_optFix`, by
  operator comparison). So the sSup is attained, which rules out the junk `sSup` of an unbounded set.
- **`RowAttains`** holds for both balls whenever σ ≥ 0: `tvBall_rowAttains` uses compactness, and `chiBall_rowAttains`
  uses `qChiBall_extrema_attained`.

## 4. Proof soundness at the key points (check 3)

The Lean kernel checks the proofs; this section checks that the mathematical route is the right one and has no
shortcut.

- **Decomposition** (`GapBound.gap_le`). V⋆ − V^{π̂} = (Z_A − Y_A) + (Y_A − Y_B) + (Y_B − Z_B), where
  Y_A = V̂^{π⋆}, Y_B = V̂⋆ and Y_A ≤ Y_B.
  - `caseA_le`/`caseB_le` route the terms through the resolvent of a true worst-case kernel (`WorstKernel`).
  - The planning residual is ξ(t) = V̂⋆(t) − Q̂⋆(t, π̂(t)) ∈ [0, 2γ^T/(1−γ)] (`Planning.greedy_residual_bounds`).
  - The data-dependent V̂^{π̂} never enters the deviation terms. The decomposition is clean.
- **Corrected count** (`Planning.pow_le_sq_of_iterations`). From T ≥ 2 log(N/(1−γ))/(1−γ) it derives
  γ^T ≤ ((1−γ)/N)², so Ξ ≤ 2(1−γ)/N². The hypothesis `hT` is fed directly from the statement's T binder
  (`Thm72Main.lean:84`, `Thm74Main.lean:128`).
- **Lemma V** (`ResidualVariance.residual_variance_bound`) gives γ² R Var_K(Y) ≤ 2B/(1−γ) + 2B R ep, for a
  one-sided residual and Y ≥ 0 with span ≤ B. It feeds `selfBound`, and `scalar_selfBound` closes the quadratic.
- **Variance transfer** (`VarianceTransfer.lean:59`, `:80`) has the exact plan constants.
  - TV: Var_p ≤ Var_q + σS².
  - χ²: Var_p ≤ Var_q + (√σ/2)S².
  - For TV, `hspan` uses the empirical span B' = 1/(1−γ+γσ) (`TVSpan`).
- **Leave-one-out absorbing family.**
  - `absorbFamily` overrides every row at x with the singleton {δ_x}. Reward is (1−γ)u, clamped, at x.
  - `empFam_offState`/`absVal_offState` show the absorbing value equals itself recomputed from
    `completeOffStateData x N (offStateData x N data)`. This is a structural rewrite: rows with s ≠ x read only
    samples with state ≠ x.
  - The good-event family `clipFamily … code` (and `chiFamily`, which may also depend on the fixed action a) is
    defined as a function of the off-state code alone.
  - Independence comes from the accepted library lemma `offStateData_indep_empiricalRow`, an `IndepFun` under
    `samplingLaw`. It is consumed by `randomFamily_bernstein_success_gt` (`GoodEvent.lean:67–80`).
  - So independence from row (x,a)'s samples is genuinely proved, not assumed.
  - π⋆ = `optPolicy (ballFamily ball M σ) M` is data-free.
  - Coincidence at u = V̂(x) and 1-Lipschitzness in u give the grid cover with i ≤ N (`exists_grid_close`).
- **Union-bound sizes.**
  - TV: ι = Bool × Fin(N+1) × Fin(N+1), |ι| = 2(N+1)².
  - χ²: ι = Bool × Bool × Fin(N+1)², |ι| = 4(N+1)².
  - The per-row confidence is η = δ/(SA) (`allRows_indexed_bernstein'`, strict `< δ` failure), and
    ℓ = log(4|ι|SA/δ).
  - The bounds ℓ ≤ 17 L (TV) and ℓ ≤ 9 L (χ², which needs SA ≥ 2) are proved in the Numerics files.
- **Constants.** C1 = c1 = 2 and C2 = c2 = 10⁶. `tv_selfBoundExpr_le` and `chi_selfBoundExpr_le` are compiled real
  arithmetic, and the final step is `hgap.trans hnum`.
- **χ² with A = 1** (`Thm74Main.lean:35–51`). Under `Subsingleton Action`, `pick data = optPolicy`, so the gap is 0 ≤ ε
  for every data set and the probability is 1. No hypothesis is added; S = 1 with A ≥ 2 falls in the main branch with
  SA ≥ 2.
- **Why the line count is small.** The builder reused large accepted library pieces:
  - the Lemma 7.1 duals (`RobustRL.TVSourceMaximum`, `RobustRL.ChiSquaredSourceMaximum`);
  - the Chapter 3 leave-one-out independence and Bernstein machinery;
  - the variance-resolvent bridge.

  All of these are tracked and imported by `Formalization.lean`, so they fall under the main axiom audit. I found no
  shortcut.

## 5. Non-vacuity (check 4)

`<reviewer probe folder>/NonVacuity.lean` compiles with exit 0 and standard axioms. It takes the instance S = A = 2, uniform
nominal rows (so the data are genuinely random), and reward 1[a = 0], γ = 1/2.

For **whatever constants** the existential returns, it builds N = n² with n = ⌈2D√K⌉ + 1, using log y ≤ 2√y. It sets
T = ⌈C₁ log(N/(1−γ))/(1−γ)⌉ and takes a greedy pick from `Finite.exists_max`. Then it discharges every hypothesis
and obtains the conclusion under `samplingLaw`:
- `tv_fires`: σ = 1/2, δ = 1/2, ε = 1, so the probability is ≥ 1/2.
- `chi_fires`: σ = 1, δ = 1/2, ε = 1, with A = 2, so it exercises the nontrivial branch.

So the hypothesis sets are jointly satisfiable independently of the hidden constants.

## 6. Compilation (check 5)

Every command was run with `bash scripts/lean-local.sh <file>`: foreground, one file at a time, no `-o`, no lake and
no LSP.
- **All 23 modules** re-elaborated from source in dependency order: exit 0, 0 errors, 0 `sorry`. Per-file times
  are in `<reviewer probe folder>/recompile.log`; the largest is `Thm74Numerics` at 39 s.
- **Olean freshness.** Every olean is newer than its source, and every importer's olean is newer than its imports'
  oleans.
- **Probes.** `DiffProbe.lean` exits 0. `AxiomProbe.lean` exits 0 and reports
  `thm7_2_corrected_holds` and `thm7_4_corrected_holds` → `[propext, Classical.choice, Quot.sound]`.
- **Red flags.** `grep` for sorry, admit, axiom, native_decide, implemented_by, extern, unsafe and opaque in the WIP
  finds nothing. The only `set_option` is `linter.unusedSectionVars`.

## Findings

1. **(info) The statement is faithful.** The only change is the C37 iteration-count binder. This was verified by a
   textual diff, by `rfl`/`↔` (DiffProbe) and by re-elaboration.
2. **(info) Non-vacuity was established for every constant choice** (§5).
3. **(low, integration) Statement-index rules.** When the Props move into `Formalization/Statements/Ch7.lean`:
   - keep their bodies byte-identical;
   - keep `Ch7.lean` importing only definition modules (`Ch7PrintedStatements` is definitions-only);
   - add `Ch7Proofs.lean` wrappers that only apply `DRVI.thm7_*_corrected_holds`;
   - re-run DiffProbe against the integrated names;
   - re-run the axiom audit through `Formalization.lean`.
4. **(low, disclosure) Points for COVERAGE and SOURCE-ISSUES C37:**
   - the constants proved are C1 = c1 = 2 and C2 = c2 = 10⁶;
   - the corrected count is a minimal edit, and tightness of the log factor is not shown (the Statement docstrings
     already say this);
   - the oracle-planner Remarks 7.x (`:361–372`, `:453–457`) and history-dependent policies (R0f) are not covered.
5. **(info) The `local instance … MeasurableSpace State := ⊤` pattern** matches the accepted printed transcription.
   It is the discrete σ-algebra on a finite type, so it is harmless.
6. **(info) The STATUS deviation notes** (constant 8 in (S); χ² net term; ℓ ≤ 17L / 9L) are internal and do not affect
   the statement. Lean confirms the final arithmetic.

## Required edits

None blocking. For integration, follow finding 3. For disclosure, follow finding 4.

## Appendix: other module hashes (sha256)

```
87f73fdf…b3fc DualDeviation   30a517b4…3bd1 GapBound        cda1097d…c1f6 GoodEvent
523af8c1…488  LooFamily       04e4e934…d596 Optimality      6b0148bb…ba51 Planning
8edcd58b…c2e3 PolicyEvaluation 473407ed…9de9 ResidualVariance ab17206f…e9fe RobustAbsorbing
31a61c85…6d1  RowDeviation    e9fe3f89…7bf2 RowSets         8f98a4a2…ff3  SelfBound
07510d53…ae6a TVSpan          f09a4717…cd4f Thm72           ab14432d…54ca Thm72Numerics
b399a861…bffa Thm74           9d6d4909…47fdc Thm74Numerics  e7c896ab…9c488 VarianceTools
a261a737…1aed VarianceTransfer df091cce…aa1ec WorstKernel
```
