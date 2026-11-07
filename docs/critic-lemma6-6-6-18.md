# CRITIC: Lemma 6.6 (`lem:Bernstein-infinite`) and Lemma 6.18 (`lem:Bernstein-infinite-proof`)

Public copy of the independent critic report; local paths removed.

- Date (UTC): 2026-11-06 23:07Z onward
- Reviewer: an independent Claude critic subagent that did not build this code
- Git HEAD: `50555485a4c7b5aac4710965a63bbd5e86d6c73b`, branch `recovery-batch-fano-ch2-ch6-20261106`. The reviewed modules are untracked working-tree files.
- Method: source and text only. I ran no Lean, lake, compiler or lean-lsp. Compilation and axiom evidence come from the builder's `<builder working folder>/BUILD-LOG.md`, runs 28–33. I did not reproduce them.
- Order of work: I wrote my source reconstruction and comparison before reading `BUILD-LOG.md` and `the private independent check note (C23-covering-set)`. I did not read `the private preflight note (Lemma6_6)`, the PROGRESS files or other CRITIC files.

## SHA256

| File | sha256 |
|---|---|
| `source/upstream/tex/chapters/offlineRL.tex` | `67cf0d1ce6a3d7c6cc43aedb371c692a3da0508193d735609713b03c0186f1e4` (matches `source/provenance.json`) |
| `Formalization/OfflineRL/VILCBDatasetDefinitions.lean` | `c222a783113685286c99ff385ea24748a575c859a6d88297e7b9b67a7d05638d` |
| `Formalization/OfflineRL/BernsteinInfiniteFixedRow.lean` | `3184972cc188cb102497f1137011a1868692a526e42916e153742c0d4898fc15` |
| `Formalization/OfflineRL/VILCBAuxiliaryAbsorbing.lean` | `d04522f46c605ab2208b9262882beb488e1cbbb0b4d3775191a945611927bb5f` |
| `Formalization/OfflineRL/BernsteinInfiniteCover.lean` | `12136ade9c617eb6383b06c3d5976e24256d4e3c2826a3dff23590885c93716b` |
| `Formalization/OfflineRL/BernsteinInfiniteData.lean` | `9a6ba43a1829bd3c62de5dc35f5240dfbc88a50cfbddeb9d545a8efaf586ceb6` |
| `Formalization/Probability/VarianceIccPerturbation.lean` | `ab1dc8e78a8cef664f8ac9af0b89c5fbe43b31ba04cc86ed1d528cbed7e16a11` |
| `Formalization/OfflineRL/VILCBDefinitions.lean` (penalty, `T_pess`) | `dc1103c296de8ed755007b72d8a441f4e81ae68e667908aaa321effaf71a99b6` |
| `<builder working folder>/StatementProbe.lean` | `745301e243b6fa6d5c093a60a626117c0007beb8ecb00da6b9151ae51e930c8b` |
| `docs/SOURCE-ISSUES.md` (working tree) | `fe83f77b754a018199f81b5414d9434bbc142c604813c3c1fab9836fd560456c` |

All six library hashes and the probe hash match the final hashes in BUILD-LOG.

## Source reconstruction

**Data model** (`:28–37`). There are `N` independent triples: `(s_i,a_i) ~ ρ` and `s_i' ~ P(·|s_i,a_i)`. The count is `N_{s,a} = Σ_i 1{(s_i,a_i)=(s,a)}` (`:676–678`). The empirical kernel is `P̂(s'|s,a) = N_{s,a}^{-1} Σ_i 1{(s_i,a_i,s_i')=(s,a,s')}` if `N_{s,a}>0` and `1/S` otherwise (`:685–695`).

**Penalty** (`:811–823`):

`b(s,a;V) = min{max{√(c_b log(N/((1−γ)δ)) Var_{P̂_{s,a}}(V)/N_{s,a}), 2c_b log(N/((1−γ)δ))/((1−γ)N_{s,a})}, 1/(1−γ)} + 5/N`

It has `c_b > 0` and `δ ∈ (0,1)`. For `N_{s,a}=0`, `b = 1/(1−γ)+5/N`. The operator is `T_pess(Q)(s,a) = max{r + γP̂_{s,a}V − b(s,a;V), 0}` (`:714`). `V̂⋆_pe` is the value of its unique fixed point. Lemma 6.2 gives that fixed point, and the formal version of Lemma 6.2 needs `γ ≥ 1/2` (C10).

**Lemma 6.18** (`:3635–3662`, proof `:4339–4405`). Take `δ ∈ (0,1/8)` and a fixed pair `(s,a)` with `N_{s,a}>0`. Let `V` be independent of `P̂_{s,a}` with `0 ≤ V ≤ 1/(1−γ)`. Then, with probability at least `1−8δ`:

- (a) `|(P̂−P)_{s,a}V| ≤ √(4 Var_{P̂}(V) log(1/δ)/N_{s,a}) + 5 log(1/δ)/((1−γ)N_{s,a})`
- (b) `Var_{P̂}(V) ≤ 2Var_P(V) + 5 log(1/δ)/(3(1−γ)²N_{s,a})`

Proof outline: (a) is deterministic when `N_{s,a} < 5log(1/δ)`. Otherwise the empirical Bernstein inequality at `1−4δ` applies. (b) applies Bernstein at `1−4δ` to the centered square, then the variance identity and AM-GM. A union bound gives `1−8δ`.

How the book reads it: the source uses Lemma 6.18 *conditionally on the counts* (`:1126–1128`, `:3970`). Given `N_{s,a}=n`, `P̂_{s,a}` is the empirical row of `n` iid draws from `P_{s,a}`, and "independent" means conditionally independent given the counts.

**Lemma 6.6** (`:1147–1163`, proof `:3630–4273`). Assume `γ ∈ [1/2,1)` and `δ ∈ (0,1)`, with the *same* `δ` as in the penalty that defines `V̂⋆_pe`. Let `ℓ = log(4N/((1−γ)δ))`. Then, with probability at least `1−δ`, the following hold simultaneously for all `(s,a)` and every `Ṽ` with `‖Ṽ−V̂⋆_pe‖∞ ≤ 1/N` and `‖Ṽ‖∞ ≤ 1/(1−γ)`:

- `|(P̂−P)_{s,a}Ṽ| ≤ √(8ℓ Var_{P̂}(Ṽ)/N_{s,a}) + 26ℓ/((1−γ)N_{s,a})`
- `Var_{P̂}(Ṽ) ≤ 2Var_P(Ṽ) + 24ℓ/((1−γ)²N_{s,a})`

The proof says the case `N_{s,a}=0` holds "trivially" (`:3632`). That is only true under a `x/0 = +∞` reading. Proof outline:

- Step 1: build the absorbing auxiliary MDPs `M^{s,u}`.
- Step 2: `u⋆ = (1−γ)V̂⋆_pe(s) + min_a b^{s,u}(s,a)` reproduces `V̂⋆_pe`.
- Step 3: use the grid `{i/N : 1 ≤ i ≤ ⌊N u_max⌋}`. Its size is at most `2N/(1−γ)` *only if `N ≥ 5`* (C23). Apply Lemma 6.18 at confidence `(1−γ)δ/(16N²)` and union-bound over at most `N` pairs.
- Steps 4–5: perturbation arguments give the constants 26 and 24.

## Comparison: Lemma 6.18 (`ProbeCh6.Lemma6_18`)

| Field | Source | Lean entry | Verdict |
|---|---|---|---|
| Space and law | conditional on `N_{s,a}=n`: `n` iid draws from `P_{s,a}` | any probability space `(Ω,μ)`, `draw : Ω → Fin n → S` measurable (⊤ on `S`), `μ.map draw = d.sampleMeasure n` (`Measure.pi` of `d.rowMeasure`) | faithful encoding of the conditional law |
| `N_{s,a} > 0` | yes | `n : ℕ`, `hn : 0 < n` | match |
| Independence | `V` independent of `P̂_{s,a}` | `IndepFun V (empiricalRow n hn ∘ draw) μ` with ⊤ on rows | faithful: the row has finite range, so the ⊤ σ-algebra on rows gives `σ(P̂)`. Independence from the row is enough, because both events depend only on `(P̂, V)`. It does not demand independence from the raw draws. |
| `V` | random vector, `0 ≤ V ≤ 1/(1−γ)` | `V : Ω → S → ℝ` measurable, `∀ ω s, 0 ≤ V ω s ∧ V ω s ≤ 1/(1−γ)` | match (measurability is standard) |
| `γ` | standing `γ ∈ [0,1)` | `0 ≤ γ → γ < 1` (the export needs only `γ < 1`) | match |
| `δ` | `δ ∈ (0,1/8)` | `0 < δ`, `δ < 1/8` (both strict) | match |
| Probability | "at least `1−8δ`" | `1 − 8δ ≤ μ.real {…}` (the export proves `<`; the wrapper uses `.le`) | match |
| (a) | `√(4 Var_{P̂}(V) log(1/δ)/N) + 5log(1/δ)/((1−γ)N)` | `√(4·Var·log(1/δ)/n) + 5·log(1/δ)/((1−γ)·n)` | exact |
| (b) | `2Var_P(V) + 5log(1/δ)/(3(1−γ)²N)` | `2·d.variance + 5·log(1/δ)/(3(1−γ)²·n)` | exact |
| Joint event | both inequalities simultaneously | `∧` inside one set | match |
| Measurability of the event | – | the export proves both sets measurable (`measurableSet_event`), so `μ.real` is a genuine measure and not an outer-measure bound | OK |
| Junk values | – | `log(1/δ) > 0`; the `√` argument is ≥ 0; `n > 0` cast to ℝ; `Var` is the true finite variance | none |

## Comparison: Lemma 6.6 (`ProbeCh6.Lemma6_6`)

| Field | Source | Lean entry | Verdict |
|---|---|---|---|
| Dataset | `N` independent triples, `(s,a) ~ ρ`, `s' ~ P(·|s,a)` | `X : Ω → Fin p.N → (S×A)×S` measurable (⊤), `iIndepFun` coordinates, each marginal `Σ_t ofReal(ρ(t.1)·P(t.2|t.1))•δ_t` | match (same encoding as the Lemma 6.5 entry; `iidTriples_map_eq_jointRow` proves it equals the product law) |
| `N` | `N ≥ 1` implicit | `p.N`, `N_pos` | match |
| Counts and `P̂` | `:676–695`, uniform `1/S` when unseen | `dataCount` = filter-card; `dataPhat` = `N_{s,a}^{-1}Σ_i 1{x_i=((s,a),t)}`, else `uniformRow` (`1/card S`) | exact |
| Penalty | `def:bonus-Bernstein-infinite` with the zero-count convention, `c_b>0`, `δ∈(0,1)` | `Input.bonus`, `logTerm = log(N/((1−γ)δ))`, `count = 0 ⇒ 1/(1−γ)+5/N` | exact |
| Rewards | known, in `[0,1]` | `Params.r` in `[0,1]` | match |
| `V̂⋆_pe` | value of the unique fixed point of `T_pess` | `∀ Qstar, pess Qstar = Qstar → … value Qstar` | equivalent: a fixed point exists and is unique for `γ ≥ 1/2` (`lem_monotone_contraction_corrected`), so the statement is not vacuous |
| `γ` | `γ ∈ [1/2,1)` | `1/2 ≤ p.γ`, `p.γ < 1` | match |
| `δ` coupling | the same `δ` in the penalty and the event | `p.δ` in both (the export is more general, with an event level `δ'`) | match |
| Range of `Ṽ` | `‖Ṽ−V̂⋆_pe‖∞ ≤ 1/N`, `‖Ṽ‖∞ ≤ 1/(1−γ)`, inside the event | `∀ t, |Vt t − value Qstar t| ≤ 1/p.N` (real division, because the `binrel%` leaves are cast to ℝ), `∀ t, |Vt t| ≤ 1/(1−γ)` | match. `Ṽ` may be negative, as in the source. |
| Simultaneity | all `(s,a)` and all `Ṽ` inside one event | `∀ Qstar s a Vt` inside the set | match |
| `N_{s,a}` | all pairs; `N_{s,a}=0` "trivial" (`:3632`) | `0 < count s a →` | **encoding of the +∞ reading; needs disclosure (MINOR-1)** |
| Constants | `√(8ℓ/N_{s,a}·Var)`, `26ℓ/((1−γ)N_{s,a})`, `24ℓ/((1−γ)²N_{s,a})`, `ℓ = log(4N/((1−γ)δ))` | identical | exact |
| Probability | "at least `1−δ`" | `1 − p.δ ≤ μ.real {…}` | match. The set is `X⁻¹'(goodSet)`, with `goodSet` a subset of a finite type, so it is measurable. |
| Hidden premises | – | `Nonempty S`, `Nonempty A` (needed for `max_a` and `1/S`) | none substantive |

## Proof honesty

- **Wrappers.** `Lemma6_18_holds` is `(bernsteinInfinite_fixedRow …).le`. `Lemma6_6_holds` is `bernsteinInfinite_iid p hγ ρ P μ p.δ p.δ_pos p.δ_lt_one X hX hind hmarg`. Each only applies the export, with no restated proof. The `Lemma6_6` set matches `{ω | X ω ∈ goodSet p P p.δ}` with `Lemma66Bound` unfolded, textually up to `p.input` field projections. According to the builder log (run 33), `exact` closes it. I did not re-run this.
- **Axioms grep.** I computed the import closure of the probe's two imports: 85 project modules. A grep of all of them for `sorry|admit|axiom|opaque|implemented_by|unsafe|native_decide|ofReduceBool|@[extern` found **no hits**. The builder reports `#print axioms` = `[propext, Classical.choice, Quot.sound]` for both wrappers and both exports (runs 20, 29, 33). I did not re-run this.
- **Leave-one-out layer.** I checked this by reading the code.
  - `auxPess` at `s' ≠ s` reuses the original `T_pess`, so it reads only `P̂` rows at states other than `s`.
  - `auxFix_emit_offState` and `indep_offState_draw` give independence from `P̂_{s,a}` for fixed labels. The transition stack has independent coordinates, and the off-`s` and on-`s` coordinate sets are disjoint.
  - `uMax`/`uGrid` depend only on counts (`uMax_emit`, `uGrid_emit`).
  - `u_max = min_a bonusAbs + 1` equals the source's `min{2c_bℓ'/((1−γ)max_a N_{s,a}), 1/(1−γ)} + 5/N + 1`. `bonusAbs` is monotone in the count, and the zero-count convention gives `1/(1−γ)+5/N`.
  - The union bound uses `δ₂ = (1−γ)δ'/(16N²)`, with `δ₂ < 1/8` checked. There are at most `N` pairs with count ≥ 27 (image of the labels), and the grid has at most `2N/(1−γ)` points when `N ≥ 5`. The total is `N·(2N/(1−γ))·8δ₂ = δ'`.
  - The bound is integrated over labels by `Measure.prod_apply` and transported to `X` by `map`. This matches `:3969–3990`, with the source's "at most N pairs" made rigorous by conditioning on labels.
- **C23 repair is sound.** The formal proof does not split on `N ≤ 4`, as C23's text proposes. It splits *per pair* at `N_{s,a} ≥ 27`, which forces `N ≥ 27 ≥ 5`, so `uGrid_card_le` applies. For `1 ≤ N_{s,a} ≤ 26`, `lem66_small_count` gives both bounds surely:
  - `γ ≥ 1/2`, `δ < 1` and `N ≥ 1` give `ℓ > log 8 > 2`.
  - `|(P̂−P)Ṽ| ≤ 2/(1−γ) ≤ 26ℓ/((1−γ)N_{s,a})` because `N_{s,a} ≤ 13ℓ`.
  - `Var_{P̂}(Ṽ) ≤ E Ṽ² ≤ 1/(1−γ)² ≤ 24ℓ/((1−γ)²N_{s,a})` because `N_{s,a} ≤ 48 ≤ 24ℓ`.

  I re-derived this by hand. I also re-checked C23's counterexample: `N=1`, `γ=1/2`, `c_b=1`, `δ=0.1` gives `u_max = min{4 log 20, 2} + 6 = 8`, so `|U| = 8 > 4`. That is consistent with `the private independent check note (C23-covering-set)`, which I read after writing the comparison above.

## Findings

**BLOCKING:** none.

**MAJOR:** none.

**MINOR-1: the zero-count encoding needs a disclosure.** `Lemma6_6` adds `0 < N_{s,a} →`. The printed statement quantifies over all pairs and divides by `N_{s,a}`. The source's own proof (`:3632`) says the `N_{s,a}=0` case "holds trivially", which only makes sense with right-hand side `+∞`. The restriction loses nothing under that reading. Under Lean's literal `x/0 = 0` reading, the printed statement is **false**, so the hypothesis is necessary.

Failure scenario:
- `S = {1,2}`, one action, `ρ = δ_{(1,a)}`, `P(·|1,a) = δ_1`, `P(·|2,a) = δ_1`, `r(1)=1`, `r(2)=0`, `N` large, `Ṽ = V̂⋆_pe`.
- Then `N_{2,a}=0` almost surely and `P̂(·|2,a) = (1/2,1/2)`.
- `V̂⋆_pe(2) = 0`, because the bonus `1/(1−γ)+5/N` clips it.
- `V̂⋆_pe(1) = (1−b)/(1−γ) > 0`, where `b = min{2c_bℓ'/((1−γ)N), 1/(1−γ)} + 5/N < 1`.
- The left side is `V̂⋆_pe(1)/2 > 0`, but both literal right sides equal `0`. The literal variance claim `V̂⋆_pe(1)²/4 ≤ 0` also fails. The event fails with probability 1.

This is the same kind of disclosure as C18 (a zero-count convention). Under the AGENTS rule it is not a `_restricted` mismatch: the export implies the printed result under the source's own stated reading. It must still be disclosed (text below). If the lead considers the `+∞` reading an interpretation rather than the printed statement, rename the entry `Lemma6_6_restricted`. I accept either choice if the disclosure is present.

**MINOR-2: docstrings are too thin for the statement index.**
- The probe's `Lemma6_6` docstring says "positive-count encoding" but does not say:
  - why the zero-count case is excluded;
  - that the penalty `δ` and the event `δ` are the same `p.δ`;
  - that "every fixed point" stands for the unique `V̂⋆_pe`, with uniqueness and existence from the corrected Lemma 6.2 under `γ ≥ 1/2`;
  - that the printed proof has the C23 gap.
- The `Lemma6_18` docstring does not say that the entry is the conditional-on-`N_{s,a}=n` encoding (`:1126–1128`, `:3970`) on an abstract space, or that independence is required only from the empirical row.

Suggested text is below.

**MINOR-3: the C23 entry describes a different repair from the one implemented.** C23 proposes "if `N ≤ 4` the conclusions hold surely; otherwise Steps 3–5 apply". The formal proof splits per pair at `N_{s,a} ≤ 26` vs `≥ 27`. Both are sound, and C23 already states the `1 ≤ N_{s,a} ≤ 26` deterministic fact. Add a "Formal handling" line so the ledger matches the code.

**NOTE-1: integration imports.** In `Formalization/Statements/Ch6.lean`, only `Formalization.OfflineRL.VILCBDatasetDefinitions` needs to be added. `FiniteSampleDefinitions` is already imported. Do not import `BernsteinInfiniteData` into `Ch6.lean`; it belongs only in `Ch6Proofs.lean`. `VILCBDatasetDefinitions` contains only the probability-vector obligations of `uniformRow`/`dataPhat`, which is acceptable for a definitions module.

**NOTE-2: extra premises.** `Lemma6_18` includes `0 ≤ γ`. The export does not need it, but it is the chapter's standing discount convention, so it is not a hidden premise. The penalty constant `c_b > 0` is universally quantified. The source needs no largeness of `c_b` for this lemma, so this is at least as strong as printed.

**NOTE-3: verification limits.** I did not compile anything. The `exact` defeq match between `Lemma6_6` and `goodSet`/`Lemma66Bound`, the Step 4–5 scalar algebra (`steps45_scalar`, `VarianceIccPerturbation`), and the axiom closure rest on the builder's logged runs 15–33, not on an independent rebuild. The public check `python3 scripts/check.py` after integration should confirm them.

## Required disclosure text (proposed `SOURCE-ISSUES.md` scope bullet)

> - Lemma 6.6 (`lem:Bernstein-infinite`, `offlineRL.tex:1147–1163`) is indexed as `Lemma6_6` with the
>   premise `0 < N_{s,a}` on each pair. The printed bounds divide by `N_{s,a}`; the source proof
>   (`:3632`) declares the `N_{s,a} = 0` case trivial, which holds only when the right-hand sides are
>   read as `+∞`. Under Lean's `x/0 = 0` the printed inequalities are false for unseen pairs (for
>   example, a never-sampled pair whose uniform row `1/S` sees two states with different `V̂⋆_pe`
>   values), so the entry states exactly the positive-count content. The penalty and event share
>   the parameter `δ`; `V̂⋆_pe` is any fixed point of `T_pess`, which exists and is unique for
>   `γ ≥ 1/2` (corrected Lemma 6.2, [C10](#C10)). The printed proof's covering-set bound assumes `N ≥ 5`
>   ([C23](#C23)); the formal proof instead treats pairs with `N_{s,a} ≤ 26` deterministically and
>   applies the grid argument only when `N_{s,a} ≥ 27`.
>
> - Lemma 6.18 (`lem:Bernstein-infinite-proof`, `offlineRL.tex:3635–3662`) is indexed as `Lemma6_18`
>   in its conditional-on-counts form: for a fixed `n = N_{s,a} > 0`, `P̂_{s,a}` is the empirical row of
>   `n` iid draws from `P_{s,a}` on an arbitrary probability space, and `V` is independent of that row
>   (`:1126–1128`, `:3970–3972`).

Suggested C23 addition:

> **Formal handling:** the formal proof splits per pair. When `1 ≤ N_{s,a} ≤ 26`, both conclusions hold
> surely (`lem66_small_count`). When `N_{s,a} ≥ 27`, the inequality `N ≥ 27 ≥ 5` validates the printed
> grid bound (`uGrid_card_le`).

## VERDICT

- **Lemma 6.18 (`Lemma6_18`): ACCEPT.** The statement is faithful to the conditional reading used by the source, the constants and endpoints are exact, and the wrapper only applies the export. Add the docstring clarification from MINOR-2.
- **Lemma 6.6 (`Lemma6_6`): ACCEPT WITH REQUIRED DISCLOSURE.** The statement is faithful on every field except the zero-count encoding (MINOR-1). That encoding is correct under the source's own `+∞` reading and necessary under Lean's semantics, but it must be disclosed (bullet above) before or with integration. The C23 repair is sound. No blocking or major issues.
