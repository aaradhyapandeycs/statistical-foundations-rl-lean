# CRITIC — Theorem 6.13 (`thm:infinite-lwoer-bound`) statement entry `Thm6_13`

Public copy of the independent critic report; local paths removed.

- Date (UTC): 2026-11-06 22:41–22:55 UTC
- Reviewer: independent Claude critic subagent (did not build this code)
- Git HEAD: `50555485a4c7b5aac4710965a63bbd5e86d6c73b` (branch `recovery-batch-fano-ch2-ch6-20261106`; reviewed files are uncommitted/untracked working-tree state)
- Mode: source-only; no Lean (no lake/lean/LSP run by this critic). Python used only for numeric sanity checks (`python3 -I`, scripts in the session scratchpad).
- Order: reconstruction and comparison written before reading `the private preflight note (Thm6_13)`, the builder brief, `<builder working folder>/`, PROGRESS or other CRITIC files. Only `<builder working folder>/BUILD-LOG.md` was read afterwards (last section).

## SHA256

| File | SHA256 | Expected prefix | Match |
|---|---|---|---|
| `source/upstream/tex/chapters/offlineRL.tex` | `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4` | `source/provenance.json` line 39 | yes |
| `Formalization/Statements/Ch6.lean` | `708fa4241f18ff51fbf1c613030f4222f40c901e746d32b6eb8d29590ad1799f` | `708fa424…` | yes |
| `Formalization/Statements/Ch6Proofs.lean` | `d59146ced3920dd4277b61d73b495b577798cbcf9be5ca58f9cb5399fcb31535` | `d59146ce…` | yes |
| `Formalization/OfflineRL/LowerBoundMinimax.lean` | `f846191e1c97dd96d2c8416a995e9bdd4878170cf3ed9e315b73961a5ba03d1a` | `f846191e…` | yes |
| `Formalization/OfflineRL/LowerBoundDataKL.lean` | `b8d7195d56e3dea680bc2a2a17f2d1db33f73369f7dec292c80a468ac614f914` | — | — |
| `Formalization/OfflineRL/LowerBoundConcentrability.lean` | `be1b693db04d55d3718eea244b6b1c6131f22d798663dc92a00f8b1dc3ddac10` | — | — |
| `Formalization/OfflineRL/LowerBoundValueGap.lean` | `6643925819bab1c4cd54995392dec77c4e01b536af4b8461dd5365e3be73b166` | — | — |
| `Formalization/Probability/Fano/HammingPacking.lean` | `a44309ede27fe121c5aaf26c3a131434e857753a5dc2a34daa779922b4dff4f2` | — | — |
| `Formalization/Probability/Fano/FanoLemma.lean` | `cd842c006dfc78af52f002f93733931ece6ba263bf335f2fced6006736fb758d` | — | — |

## Independent source reconstruction (`offlineRL.tex`)

**Statement (2367–2402).** For any `(γ, S, C⋆, ε)` with `γ ∈ [2/3, 1)`, `S > 12`, `C⋆ > 2`, `ε ≤ 1/(672(1−γ))`:
there exist a class `{M_θ : θ ∈ Θ}`, each with `S` states and 2 actions, a test distribution `ρ ∈ Δ(S)`, and a batch dataset of `N` independent samples whose single-policy concentrability coefficient lies in `[C⋆, 2C⋆]` (closed interval in the theorem), such that
`inf_π̂ max_θ P_{M_θ}(V⋆_θ(ρ) − V^π̂_θ(ρ) > ε) ≥ 1/4`, provided `N ≤ c₂ S C⋆ / ((1−γ)³ ε²)` for some universal `c₂ > 0`. Infimum over all policy estimators. The macro `\Cstar` = `C^⋆_ρ` (commands.tex:244) is used both for the parameter and the coefficient; the only coherent reading is "parameter `C⋆`, coefficient `C⋆_ρ ∈ [C⋆, 2C⋆]`".

**Data model (31–39).** `D = {(s_i,a_i,s_i')}`, `(s_i,a_i) ~ d^b` independent, `s_i' ~ P(·|s_i,a_i)`. **Concentrability (128–140).** `C⋆_ρ = max_{(s,a)} d⋆(s,a;ρ)/d^b(s,a)`, `d⋆` the discounted occupancy of the optimal deterministic policy from `ρ`, `0/0 = 0`.

**Hard instances (2432–2634).** Standing assumption `224(1−γ)ε/γ ≤ 1/2` (2445); for `γ ≥ 2/3` this follows from `ε ≤ 1/(672(1−γ))` (gives `≤ 1/(3γ) ≤ 1/2`; numerically 0.5 at γ = 2/3). States `{0,…,S−1}`, actions `{0,1}`; `μ(0) = 1 − 1/C`, `μ(s) = 1/(C(S−1))`; `P_θ` as in `eq:defn-Ptheta-defn-inf` with `p, q = γ ± 224(1−γ)²ε/γ`; rewards `1` on `s>0`, `4/7` at `(0,0)`, `0` at `(0,1)`, shared across θ; `Θ` a Gilbert–Varshamov packing (`|Θ| ≥ e^{(S−1)/8}`, pairwise distance `≥ (S−1)/8`); `d^b(s,a) = μ(s)/2` (shared across θ); `ρ` uniform on `s>0`; `C < C⋆_ρ < 2C` (strict, 2630–2633), with `C` set to the parameter.

**Proof (2638–2927).** Step 1: gap `≥ (24ε/(S−1)) Σ_s (1 − π(θ_s|s))`; a policy with gap `≤ ε` w.p. `≥ 3/4` decodes to θ (argmin decoder) w.p. `≥ 3/4`. Step 2: Fano with `M = |Θ|−1` + KL tensorization. Step 3: one-sample KL `≤ c₃(1−γ)³ε²/C` (Lemma 6.15; C21 records a mis-cited Bernoulli KL step, conclusion unaffected). Step 4: `N ≤ c₂ C⋆ S/((1−γ)³ε²)` with small `c₂` and `S > 12` gives `p_e > 1/4`, contradiction. The proof needs `ε > 0` (otherwise `p = q`, actions tie, and Step 1's decoding is vacuous) — SOURCE-ISSUES C9.

Gaps I noticed in the printed argument: (i) `ε > 0` not stated (C9); (ii) the threshold is expressed via the parameter `C⋆` in the theorem but via the coefficient `C⋆_ρ` in Step 4 (equivalent up to the factor 2 since `C⋆ ≤ C⋆_ρ ≤ 2C⋆`); (iii) "all policy estimators" is not defined (deterministic vs. externally randomized; output class).

## Comparison table (printed vs `def Thm6_13`)

| Item | Printed | Lean `Thm6_13` | Verdict |
|---|---|---|---|
| Constant quantifier | "for some universal `c₂ > 0`" | `∃ c₂, 0 < c₂ ∧ ∀ γ S C⋆ ε, …` (outermost) | faithful (universal, independent of all parameters) |
| γ range | `[2/3, 1)` | `2/3 ≤ γ → γ < 1` | exact |
| S | `S > 12` | `12 < S` (ℕ) | exact |
| C⋆ | `C⋆ > 2` | `2 < Cstar` | exact |
| ε | `ε ≤ 1/(672(1−γ))`, no lower bound | `ε ≤ 1/(672*(1-γ))`, no lower bound | exact; see C9 note below |
| Class of MDPs, S states, 2 actions | ∃ `{M_θ}` | `∃ State Fintype Θ Fintype M`, `Fintype.card State = S`, actions `Bool` | faithful; Θ nonempty forced by the `∃ θ` conclusion |
| Shared reward / discount | `M_θ = (S, A, P_θ, r, γ)` | `(M θ).discount = γ`, rewards pairwise equal; reward ∈ [0,1] built into `DiscountedMDP` | faithful |
| Test distribution ρ | ∃ ρ | `∃ ρ : FiniteDistribution State` shared across θ | faithful |
| Dataset / `d^b` | ∃ dataset of N independent samples | `∃ db` shared across θ, independent of N; law `Measure.pi (Σ_t ofReal(db(s,a)·P_θ(s'|s,a)) • dirac t)` | faithful (and uniform in N, stronger) |
| Concentrability | coefficient "lies within `[C⋆, 2C⋆]`" (theorem, closed); proof gives strict | `∀ θ, ofReal C⋆ ≤ ⨆_{sa} ofReal(d⋆_θ(sa)) / ofReal(db sa) ≤ ofReal(2C⋆)` in `ℝ≥0∞` | faithful to the theorem's closed interval; `x/0 = ∞`, `0/0 = 0` correct conventions; `d⋆` uses `optimalGreedyPolicy` (a genuine optimal deterministic policy; unique at ε>0) |
| Value / gap | `V⋆_θ(ρ) − V^π̂_θ(ρ) > ε` | `ε < Σ_s ρ(s)(V^{greedy⋆}_θ(s) − V^{π̂(D)}_θ(s))`, values = expected discounted return on the actual trajectory law; greedy proved to dominate every stationary policy (`trajectoryValue_le_optimalGreedy`) | faithful |
| Probability | `≥ 1/4` | `1/4 ≤ (law).real {D | …}` | exact |
| inf/max | `inf_π̂ max_θ` | `∀ πhat, ∃ θ` over a finite Θ | equivalent for the deterministic estimator class |
| Estimator class | "all policy estimators" | functions `(Fin N → (State×Bool)×State) → StationaryPolicy State Bool` (any function; ⊤ σ-algebra, finite space, so no measurability restriction) | see MINOR-1 |
| N threshold | `N ≤ c₂ S C⋆/((1−γ)³ε²)` | `(N:ℝ) ≤ c₂ * S * Cstar / ((1-γ)^3 * ε^2)`, `∀ N` after the instance | exact (instances uniform in N — stronger than a per-N reading) |
| Hidden premises | none | none in `Thm6_13`; wrapper adds nothing | none found |

## Findings

**BLOCKING:** none.

**MAJOR:** none.

**MINOR-1 (estimator class).** `πhat` ranges over deterministic maps from datasets to stationary randomized policies. A learner with external randomness `U` (e.g. a randomized tie-break, or a random choice among deterministic policies) is not literally covered: from "∀ deterministic πhat ∃ θ" one cannot formally deduce "∃ θ with `E_U[P_θ(…)] ≥ 1/4`", since θ may depend on `U`. Failure scenario: a reader takes the printed "inf over all policy estimators"/"no algorithm can" (2413) to include randomized algorithms; the Lean entry does not state that. Mitigation: mathematically the gap closes immediately with the same proof (`lb_fano_core` works through the θ-average of error probabilities, which is linear in the law of `U`), and deterministic estimators is the usual convention, and the book does not define the class. Not a fidelity break; recommend a one-line docstring disclosure ("deterministic estimators; externally randomized estimators are not covered by this entry") or a later strengthening.

**MINOR-2 (C9 consistency).** `docs/SOURCE-ISSUES.md#C9` says a source-facing declaration "should … make the chapter's positive-accuracy convention explicit". `Thm6_13` instead keeps the printed hypotheses (no `ε > 0`), which is strictly stronger and is disclosed in its docstring, but C9 was not updated to say so. At `ε = 0` the Lean threshold reads `N ≤ 0` (junk `x/0 = 0`), so the entry is only nontrivially informative there for `N = 0`; the docstring discloses that the "every N" reading of an undefined `…/0` is not covered. For `ε < 0` the event is certain (proved via `trajectoryValue_le_optimalGreedy`). Recommend adding one sentence to C9 pointing at `Thm6_13` and its handling. No `_restricted` suffix needed: the printed hypotheses and conclusion are stated verbatim.

**MINOR-3 (process).** `docs/COVERAGE.md` has no Theorem 6.13 row in the working tree (diff touches only `Formalization.lean`, `Ch6.lean`, `Ch6Proofs.lean`, `SOURCE-ISSUES.md`). AGENTS.md requires the statement entry and the COVERAGE "proved" record in the same change. Also the four library files and `HammingPacking.lean` are untracked. Integration must add them and the COVERAGE row together.

**NOTE-1 (threshold uses parameter vs. coefficient).** Printed Step 4 uses `C⋆_ρ` (actual coefficient), the theorem uses the parameter `C⋆`. Since `C⋆ ≤ C⋆_ρ ≤ 2C⋆` is part of the conclusion, the two readings are interchangeable by halving `c₂`. Lean uses the theorem's (parameter) form. No action.

**NOTE-2 (stationary output).** Estimator outputs are stationary (Markov) randomized policies, matching the chapter's policy notion; history-dependent output policies are not covered. Low relevance.

**NOTE-3 (constant).** `c₂ = 1/(36·16·336²) ≈ 1.54·10⁻⁸`; `c₃ = 16·336²`. Arithmetic checked: `(m+1)/36 ≤ m/32` iff `m ≥ 8` (have `m = S−1 ≥ 12`), `log|Θ| ≥ m/8`, `|Θ| ≥ e^{3/2} ≈ 4.48 ≥ 4`, `fano_large_cardinality_quarter` gives `1 − (B+log 2)/log K ≥ 1/4` under `B ≤ log K/4`, `K ≥ 4`. I also numerically checked (python, γ ∈ {2/3, .8, .95, .999}, C ∈ {2.01, 10, 10⁴}, ε at 1, .5, .01 of the max) that both directed KLs of the `s>0` rows are below `16·336²(1−γ)³ε²`.

**NOTE-4 (ε₀ construction).** For `ε ≤ 0` the library builds the family at `ε₀ = 1/(672(1−γ)) > 0`; for `ε > 0`, `ε₀ = ε`. The `ε = 0, N = 0` case is closed by the `ε₀` instance and monotonicity of the event in `ε`. Legitimate.

## Provider chain (statement → proof)

- `Thm6_13_holds : Thm6_13 := StatisticalRL.OfflineRL.LowerBound.offline_minimax_lower_bound` — the library statement is textually identical to the `def Thm6_13` body (compared line by line), so the wrapper only applies the library theorem; no restatement, no second proof.
- `offline_minimax_lower_bound` (LowerBoundMinimax.lean:300) ← `exists_gilbertVarshamov` (HammingPacking.lean:131), `lb_concentrability` (LowerBoundConcentrability.lean:277, needs `ε₀ > 0`), `trajectoryValue_le_optimalGreedy` (MDP/OptimalTrajectoryValue.lean:123, ε<0 branch), `lb_minimax_core` (:247), `pi_diracSum_eq_sampleMeasure` (:33, identifies the printed law with `jointRow … sampleMeasure`).
- `lb_minimax_core` ← `lb_fano_core` (:159) ← `PrelimFano.fano_test_average_error_lower` (FanoLemma.lean:171), `lb_dataset_klDiv_le` (LowerBoundDataKL.lean:250, KL tensorization + Lemma 6.15 constant), `GenerativeLowerBound.fano_large_cardinality_quarter`; and Step 1 via `lb_gap_ge_score` (:120) ← `lb_value_gap_state` (LowerBoundValueGap.lean:127) ← `lb_policy_value_le`, `lb_optimalValue` (Lemma 6.14 family), plus `lbDecode_eq`/`lbScore_sep`.
- Definitions checked directly: `lbMDP`, `lbRow`, `lbMu`, `lbP/lbQ/lbGap` (LowerBoundFamilyDefinitions.lean) match `eq:defn-Ptheta-defn-inf`, `eq:infinite-p-q`, `infinite-mu-assumption`, `eq:defn-r-theta-defn-inf`; `lbBehavior` = `μ(s)/2`; `lbTest` = `ρ`; `FiniteDistribution`, `DiscountedMDP`, `StationaryPolicy` (MDP/CoreDefinitions.lean), `trajectoryExpectedValue` (MDP/InfiniteReturn.lean), `optimalGreedyPolicy` (Bellman-greedy, proved optimal against all stationary policies), `discountedJointOccupancy` (MDP/DiscountedOccupancy.lean) are genuine, non-junk definitions.
- Logic of the library proof (read, not compiled by me): sound. The contrapositive in `lb_minimax_core` (gap `≤ ε` ⇒ score `≤ m/24` ⇒ decode correct, using `ε > 0` to cancel) and the per-θ Fano averaging are correct.

## Grep (import closure)

Import closure of `Formalization.Statements.Ch6Proofs` computed by a recursive import parser (project files only): 129 files (102 for `LowerBoundMinimax` alone). Pattern
`\bsorry\b|\badmit\b|^\s*(private\s+|noncomputable\s+)?axiom\b|\bopaque\b|implemented_by|\bunsafe\b|native_decide|@\[extern|ofReduceBool|decide := true`
→ **0 hits** (including comments). Local instances in `LowerBoundMinimax.lean` (`MeasurableSpace … := ⊤`, `MeasurableSingletonClass`) are ordinary, sound instances on finite types.

## Lean-side items

- `Ch6.lean` imports definition modules only (`LowerBoundFamilyDefinitions` etc.); the entry uses `DiscountedMDP`, `FiniteDistribution`, `StationaryPolicy`, `discountedJointOccupancy`, `optimalGreedyPolicy`, `trajectoryExpectedValue`, `Measure.pi` — all available from those imports per the existing file header; whether `Ch6.lean` still elaborates is a compile fact I did not check.
- `Formalization.lean` imports `Statements.Ch6`, `Statements.Ch6Proofs` (lines 710–711) and now the four new library modules and `HammingPacking`, so `Audit.lean` (namespace `StatisticalRL` prefix, allowed axioms `propext`, `Classical.choice`, `Quot.sound`) covers `Thm6_13_holds` and the library.
- Theorem signature of the library export is not weakened by the index; the wrapper is a bare term.
- No `letI` misuse: the `letI : MeasurableSpace … := ⊤` inside the Prop fixes the σ-algebra for `Measure.pi`/`dirac`; on a finite type every set is measurable, so `.real {D | …}` is the genuine probability.

## Builder BUILD-LOG consistency

Read after the sections above were written. Consistent:

- Final compile rows' source hashes equal the current hashes of every reviewed file: HammingPacking `a44309ed…`, ValueGap `66439258…`, Concentrability `be1b693d…`, DataKL `b8d7195d…`, Minimax `f846191e…`, Ch6 `708fa424…`, Ch6Proofs `d59146ce…`, `Formalization.lean` `480b072c…`, `Audit.lean` `29f6cd54…`, probe `1b25578c…` (all rechecked by me now). All final runs exit 0; the two exit-1 runs were on earlier source hashes and were superseded.
- Dependency order is respected (HammingPacking/ValueGap/Concentrability/DataKL before Minimax, then Ch6, Ch6Proofs, Formalization, Audit). Olean mtimes (17:38–17:39 local = 22:38–22:39 UTC) match the log.
- `<builder working folder>/last-output.txt` (probe output) shows `Thm6_13_holds`, `offline_minimax_lower_bound`, `lb_minimax_core`, `lb_fano_core`, `pi_diracSum_eq_sampleMeasure` depend only on `[propext, Classical.choice, Quot.sound]`; consistent with my 0-hit grep.
- Not independently verifiable from saved artifacts: the Audit message "Axiom audit passed for 9523 project declarations" (Audit stdout not saved; only the exit code is logged). Cosmetic: the Stage 4 command rows are appended inside the Stage 1–3 file table in `BUILD-LOG.md`.
- I did not run Lean; compile and axiom facts above are the builder's evidence, judged internally consistent.

VERDICT: PASS-WITH-FINDINGS
