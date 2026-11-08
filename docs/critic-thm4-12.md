# CRITIC — Thm4_12_corrected (asynchronous Q-learning, `thm:infinite-horizon-asyn`)

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-07): edits F1, F2 and F7 of this review were applied at integration, together with the F9 integration steps; the integrated index entry is definitionally equal (rfl) to the reviewed Prop. The review text below is unchanged.

Date 2026-11-07. Independent critic, not the builder. I edited nothing under `<builder working folder>/`, `Formalization/` or `docs/`.
I wrote only this file and `<reviewer probe folder>/{CriticProbe.lean,probe.out}`.

## Inputs

- **Source pin.** `source/upstream/tex/chapters/generative_model_model_free.tex` has sha256
  `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`. This equals `source/provenance.json:35`.
- **Snapshot.** `<builder working folder>/Thm412Wip.reviewed-snapshot` is byte-identical to `<builder working folder>/Thm412Wip`
  (`diff -rq` printed nothing).
- **Build log.** Every file's sha256 prefix matches the last exit-0 row for that file in `BUILD-LOG.md`. Examples:
  - StatementDraft `c1384ca28c692783`
  - StatementProofDraft `085bdfaa8fcb7d8a`
  - AsyncMain `afd2d0920a60217d`
  - AsyncDefs `1f00d9952090ebd3`
  - MarkovDefs `dda4fead320504d0`
- **Library hygiene.** Grep finds no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `extern` in the
  library files.

## Verdict: PASS for statement fidelity, definitions and proof evidence; GO to integrate

There are no blocking findings. The required edits are one docstring correction (F1) and the integration checklist
(F9). No binder is classified EXCESS.

## Source reconstruction (done before reading the Lean)

### Model (`:1898–1906`)
- The initial state `s_0` is fixed and arbitrary.
- `a_t ∼ π_b(·|s_t)`, `r_t = r(s_t,a_t)`, `s_{t+1} ∼ P(·|s_t,a_t)`.
- The pairs form a chain with kernel `K((s,a),(s',a')) = P(s'|s,a) π_b(a'|s')`.

### Algorithm (`:1928–1946`, `:1977–2001`)
- For `t = 1..T`, only the entry `(s_{t-1},a_{t-1})` changes, to
  `(1−η_t) Q_{t−1} + η_t (r + γ max_{a'} Q_{t−1}(s_t,a'))`.
- The output is `Q_T`.

### Assumption and definitions
- **Uniform ergodicity** (`:2012–2015`) follows Paulin: `sup_x TV(P^t(x,·), μ) ≤ M ρ^t` with `ρ < 1`.
- **μ_min** (`:2026`) is `min μ`.
- **t_mix** (`:2037`) is `min{t : max_{(s,a)} TV(P^t(·|s,a), μ) ≤ 1/4}`. The range of `t` is unstated.

### Rate (`:2056–2058`)
- `η_t ≡ c₁ log³T / ((1−γ) T μ_min)` for `0 ≤ t ≤ T`, "for some universal constants `0 < c₁ ≤ 1`".

### Theorem (`:2062–2086`)
- **Ranges:** `δ ∈ (0,1)`, `ε ∈ (0,1]`, `γ ∈ [1/2,1)`.
- **Hypotheses:**
  - the Assumption;
  - `T ≥ c₂ log²(SAT/δ)/μ_min · max{log³T/((1−γ)⁴ε²), t_mix/(1−γ)}`, with `c₂` "sufficiently large universal";
  - `0 ≤ Q₀ ≤ 1/(1−γ)`.
- **Conclusion:** with probability at least `1−δ`, `max_{s,a} |Q_T − Q⋆| ≤ ε`.
- **Proof:** none in the monograph (C34(3)).

## (1) Binder table for `Ch4Draft.Thm4_12_corrected` (StatementDraft.lean)

| # | Lean binder / premise | Source | Bin |
|---|---|---|---|
| 1 | `∃ c₁, 0 < c₁ ∧ c₁ ≤ 1` (outermost) | `:2058` "for some universal constants 0<c₁≤1" | SOURCE |
| 2 | `∃ c₂, 0 < c₂` (after c₁, before all instance data) | `:2071` "sufficiently large universal constant c₂>0". `∃c₂` is equivalent to "every c₂ ≥ c₂₀" because the budget is monotone in c₂ (all other factors ≥ 0 once T ≥ 1) | SOURCE |
| 3 | `S A : Type`, `[Fintype S] [Fintype A]` | finite tabular MDP | TYPING |
| 4 | `M : DiscountedMDP S A` (fields: nonempty S and A, reward in [0,1], 0 ≤ γ < 1) | `:1898` MDP; reward range is the book convention; γ<1 is part of `:2063` | TYPING/STANDING |
| 5 | `πb : StationaryPolicy S A` | `:1898` stationary behaviour policy | SOURCE |
| 6 | `μ : FiniteDistribution (S×A)` with `∑_x μ(x)K(x,y) = μ(y)` | `:2009` "its stationary distribution". Unique under UE, so quantifying over every stationary μ is equivalent | SOURCE |
| 7 | `μmin` with `(∀x, μmin ≤ μ x) ∧ (∃x, μ x = μmin)` | `:2026`, the min, attained | SOURCE |
| 8 | `tmix : ℕ`, `IsLeast {t | ∀x, tvDist (K^t x) μ ≤ 1/4} tmix` | `:2037`. ℕ includes 0, which is the stronger reading: the budget is monotone in t_mix, so this implies the `t ≥ 1` reading (`max(t_mix,1)`). The set is nonempty under UE, so no vacuity | SOURCE |
| 9 | `s₀ : S` (universal) | `:1902` initial state `s_0` | SOURCE |
| 10 | `1/2 ≤ M.discount` | `:2063` γ ∈ [1/2,1) | SOURCE |
| 11 | `∃ C r, 0 ≤ r < 1, ∀ t x, tvDist (K^t x) μ ≤ C r^t` | `assump:ergodicity-asyncQ` per Paulin §1.2. The wrapper drops it | SOURCE (STANDING assumption) |
| 12 | `0 < μmin` | C34(2) | CORRECTION |
| 13 | `1 ≤ T` | Implicit in the source: the loop runs `t = 1..T` and `log T` must be defined. Needed: at T = 0 with Lean's `log 0 = 0` the budget reads `0 ≤ 0` and the claim fails | DOMAIN (see F1) |
| 14 | `2 ≤ T ∨ 2 ≤ |S||A|` | C34(1), weakest form (docs/critic-thm4-12-plan-check.md §2.3) | CORRECTION |
| 15 | `0 < δ < 1`, `0 < ε ≤ 1` | `:2063` | SOURCE |
| 16 | budget `c₂ * log(|S||A|T/δ)^2 / μmin * max(log T^3/((1−γ)^4 ε^2), tmix/(1−γ)) ≤ T` | `:2068–2070`, natural logs. The probe confirms the casts are real-valued (`(tmix:ℝ)/(1−γ)`, not ℕ-division) and that `log T ^ 3 = (log T)^3` | SOURCE |
| 17 | `∀ Q₀, 0 ≤ Q₀ ≤ M.effectiveHorizon` (`= 1/(1−γ)`, by definition) | `:2075` | SOURCE |
| 18 | Conclusion: `1 − δ ≤ (pathLaw M πb s₀ T).real {x | ∀ s a, |iterate M η Q₀ x T s a − Q⋆ s a| ≤ ε}`, with `η = c₁ (log T)^3/((1−γ) T μmin)` | `:2077–2083` and rate `:2056` | SOURCE |

**Counts:** SOURCE 13, TYPING/STANDING 2, DOMAIN 1, CORRECTION 2, **EXCESS 0**.

**Quantifier order.** It is `∃c₁ ∃c₂ ∀(instance)`, as R2 of the plan check requires. The library form `∀c₁ ∃c₂` is
stronger and is disclosed in the docstring.

**Q⋆.** `M.trajectoryExpectedQ M.optimalGreedyPolicy` is the same Q⋆ object that the existing Ch3 and Ch4 entries
use (Ch4.lean:107, :158). `OptimalTrajectoryValue.lean` proves:
- it equals `optimalityFixedPoint` (`optimalGreedy_trajectoryQ`);
- it dominates every stationary randomized policy (`trajectoryQ_le_optimalGreedy`).

So the convention is consistent with the rest of the book.

## (2) Definitions (literal; BODY_MATCH OK, WELL_DEFINEDNESS N/A_LITERAL)

### `pairKernel`, `pairPow`, `tvDist`
- `pairKernel x y = P(y.1|x) · πb(y.2|y.1)`. This is exactly `:1906`.
- `pairPow = kpow K t` with `K^0 = I` and `K^{t+1}(x,y) = ∑_w K(x,w) K^t(w,y)`. This is the true t-step matrix,
  i.e. the law of `(s_t,a_t)` from `(s,a)`.
- `tvDist p q = ½ ∑|p−q|`. For probability vectors this equals the sup-over-events TV used by Paulin and `:2037`.

### `initLaw` and `pathLaw`
- `initLaw(s,a) = 1{s=s₀} πb(a|s₀)`.
- `pathLaw = ∑_x ofReal(ν(x₀) ∏_{i<T} K(x_i,x_{i+1})) • dirac x` on `Fin (T+1) → S×A`.
- This is the genuine finite-dimensional law of `(s₀,a₀,…,s_T,a_T)`. The probe confirms `IsProbabilityMeasure`.
- `Q_T` depends only on these coordinates. The final action `a_T` is marginalized out.

### σ-algebra
- `pairMeasurableSpace := ⊤` is a local def, not a global instance.
- The measure's type fixes `MeasurableSpace.pi` of ⊤, and every set is measurable. `.real` therefore has no
  measurability junk.

### `iterate`
- For `t+1`, only the entry `(s,a) = pathAt x t` changes. Its new value is
  `(1−η)Q_t + η(r(s,a) + γ · qLearningValue M Q_t (pathAt x (t+1)).1)`, where `qLearningValue` is the max over
  actions.
- This is exactly `eqn:async-q-learning` with the index shifted.
- The probe checks the t=1 update and the frozen off-pair entries by `simp` (definitional unfolding).
- `pathAt` clamps indices beyond `T`, but only indices ≤ T are read for `iterate … T`.

## (3) Wrapper derivation — OK

`asyncQ_exists_c₂` assumes less than the entry:
- only `TV(K^{tmix} x, μ) ≤ 1/4` (the wrapper passes `htmix.1`);
- stationarity;
- `∀x, μmin ≤ μ x`.

It does not use uniform ergodicity or attainment.

`Thm4_12_corrected_holds` instantiates the library theorem at `c₁ = 1`, discards the unused premises, and applies it.
It does not restate or re-prove anything, which matches AGENTS.md "export assumes less".

## (4) Proof spot checks — OK

### Lemma V
- `block_exp_moment_le` holds from an arbitrary initial law `lam` (IsProb): `E e^{−θV} ≤ 23/25` with
  `θ = 4/(25 b μ(z))` and `b μ(z) ≥ 8 t̄`.
- `window_visits_tail` gives `e^{θ J b μ/4} (23/25)^J ≤ e^{J/25} e^{−2J/25} = e^{−J/25}`. I checked the arithmetic.
- It is applied with `ν = initLaw` at every window start `k ℓ`, through `pathExp_window_prod_le`. That lemma
  conditions block by block, so no stationarity of the start is used. This is correct.

### `markov_freedman`
- The filtration is `prefixFiltration n τ`, with `j ↦ σ(X₀..X_{τ+j})`.
- Weights: `C j` is `DependsUpTo (τ+j)`. In `window_freedman`, `weight (visits x τ z) η n j` depends only on
  `visits` at `i ≤ j`, i.e. on `X_{τ+i}` with `i ≤ j` (`weight_congr`). So it is predictable for the increment
  `h(X_{τ+j}, X_{τ+j+1})`, and that increment is centered under `K(X_{τ+j},·)` (`hcent`, through
  `pairKernel_sum_fst`).
- The count `n` is a deterministic index, and the union runs over `n ∈ range(T+1)`. This is correct.

### Union bounds
- **Freedman family:** `|S||A| · Kep · (T+1)² · 2` events at `δ₁ = δ/(4|S||A|T(T+1)²)`. The total is
  `Kep δ/(2T) ≤ δ/2`, using `Kep ≤ T` (`fail_F`).
- **Visit family:** `|S||A| · Kep · e^{−J/25} ≤ δ/2`, using `J ≥ 50ι` (`fail_V`).

### Constants
- `c₂ = asyncC₂ c₁ = max(e^{32/c₁}, 4096)`.
- **(A1) `P_ge`:** if `log T < 32/c₁`, then `T < c₂`. But `T ≥ c₂ ι² h⁴ P³ ≥ c₂ · 16 P⁵ ≥ c₂`, using
  `P ≥ log 2 = 0.693…` and `16 · 0.693⁵ ≥ 1`. This is a contradiction, so the step is sound.
- `η ≤ 1` and `η > 0` are derived (`eta_le_one`, `eta_pos`), not assumed.

### T = 1 exclusion when `2 ≤ |S||A|`
- `tmix = 0` would force `μ(x) ≥ 3/4` for every x, which is impossible when the card is ≥ 2. So `tmix ≥ 1` and
  `μmin ≤ 1/2`.
- `budget_excludes_one` with `c₂ ≥ 4096` then refutes `T = 1`.

## (5) Junk values — none reachable

- `log T` is used only after `T ≥ 2` has been derived.
- The argument of `log(|S||A|T/δ)` is ≥ T.
- `μmin > 0` and `1−γ > 0`.
- The `IsLeast` set is nonempty under UE and its membership is part of the hypothesis.
- `effectiveHorizon = 1/(1−γ)` with `γ < 1`.
- The only junk-sensitive edge is T = 0 (`log 0 = 0`), and binder 13 excludes it.
- The σ-algebra is discrete (see §2).

## (6) Compilation (foreground, one at a time, no `-o`, no lake or lean-lsp)

| Command | Result |
|---|---|
| `bash scripts/lean-local.sh <builder working folder>/Thm412Wip/AsyncMain.lean` | OK, 9 s. One lint warning: unused variable `hη0` at :28 |
| `bash scripts/lean-local.sh <builder working folder>/Thm412Wip/StatementProofDraft.lean` | OK, 1 s |
| `bash scripts/lean-local.sh <builder working folder>/AxiomProbe.lean` | OK, 5 s. All five exports depend only on `[propext, Classical.choice, Quot.sound]` |
| `bash scripts/lean-local.sh <reviewer probe folder>/CriticProbe.lean` | EXIT 0 (`<reviewer probe folder>/probe.out`) |

`CriticProbe.lean` contains:
- (a) `example : Thm4_12_corrected := Thm4_12_corrected_holds`;
- (b) `criticReading`, my own independent transcription with explicit casts, explicit `½∑|·|`, explicit
  `kpow (pairKernel …)`, `1/(1−γ)` and `Measure … |>.toReal`. It is closed by destructuring the export (exact match
  up to defeq);
- (c) `rfl`/`simp` checks of `pairKernel`, `tvDist`, `initLaw` and the async update;
- (d) `pathLaw` is a probability measure;
- (e) non-vacuity of the structural premises on a one-state, one-action MDP: stationarity, UE (`C = r = 0`),
  `IsLeast … 0`, and μ_min = 1 attained;
- `#print axioms criticReading_holds` = `[propext, Classical.choice, Quot.sound]`.

**Not machine-checked:** that the budget holds for some T under the specific `c₂ = e^{32}`. It is satisfiable
mathematically because the right-hand side is polylogarithmic in T. For example, with S = A = 1, `log T = 100`
needs about `e^{32} · 100² · 16 · 100³ ≈ e^{58} ≤ e^{100}`. The Lean probe covers non-vacuity of every other premise.

## Findings

- **F1 (minor, required).** The docstring says "`1 ≤ T` is the printed 'positive integer `T`'". The source has no
  such phrase: grep finds no "positive integer" near `:2062–2086`. Restate it as a domain premise implicit in the
  source: iterations `t = 1..T`, and `log T` must be defined. Also note that it is necessary: at T = 0 the Lean
  budget degenerates through `log 0 = 0`.
- **F2 (info).** The docstring states "`∃ c₂ ∀ c₁` is false". Cite where this is shown (`docs/critic-thm4-12-plan-check.md` §4)
  or drop the claim from the index docstring.
- **F3 (info).** Uniform ergodicity and attainment of μ_min are printed premises the proof does not use. Keeping
  them is correct per AGENTS.md (the entry states the printed result). This is not a SOURCE-ISSUES item.
- **F4 (info).** The `t_mix` range is ℕ, including 0. This is the stronger reading and is disclosed.
- **F5 (info).** Imports. `StatementDraft` imports `Formalization.MDP.OptimalTrajectoryValue`, and through
  `AsyncDefs` it imports `Formalization.ModelFree.QLearningIterateBounds`; both contain theorems. The existing
  `Statements/Ch4.lean` already pulls both in transitively through `QLearningRobustDefinitions` and
  `QLearningSamplingDefinitions`. This is consistent with precedent, and the import is not `TVCore` (R1 satisfied).
  At integration, prefer importing them through those `*Definitions` modules.
- **F6 (info).** `Statements/Ch4.lean` declares global-pattern `local instance stateMeasurable (State) := ⊤`.
  `pathLaw`'s type fixes its own σ-algebra and `.real` takes it implicitly, so there is no clash. Re-run the
  `criticReading` exact check against the integrated entry anyway.
- **F7 (minor).** Lint: unused `hη0` in `one_sub_pow_le_exp` (AsyncMain.lean:28).
- **F8 (info).** The proof is a new formal proof (plan §3), not the monograph's argument, which is only sketched.
  C34(3) should say this once the result lands.
- **F9 (required at integration).** All of the following must land in one change:
  - move the modules from the private working folder into `Formalization/` (e.g. `Formalization/ModelFree/AsyncQ/…`), with
    definitions-only `MarkovDefs` and `AsyncDefs`;
  - put the entry in `Statements/Ch4.lean` and the wrapper in `Ch4Proofs.lean`;
  - add imports in `Formalization.lean`;
  - update the `docs/COVERAGE.md` row;
  - update `docs/SOURCE-ISSUES.md` C34: status deferred → corrected; record the weakest premise
    `2 ≤ T ∨ 2 ≤ SA` (not a bare `2 ≤ T`); record the library form `∀c₁, c₂ = max(e^{32/c₁},4096)`;
  - update `docs/PROGRESS.md` ownership;
  - delete the transient `.lake/build/lib/lean/Thm412Wip/*.olean` and `<reviewer probe folder>/` probe after recording;
  - run `python3 scripts/check.py`.

## Required edits

1. Fix the `1 ≤ T` sentence in the `Thm4_12_corrected` docstring (F1).
2. Optionally cite or drop the "`∃c₂∀c₁` is false" remark (F2) and remove the unused `hη0` (F7).
3. Integrate per F9, then re-run the exact-type probe and `#print axioms` on the integrated `Thm4_12_corrected_holds`.
