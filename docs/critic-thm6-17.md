# CRITIC — `Thm6_17_restricted` (finite-horizon LCB-Q, `thm:lcbq`) — independent critic, not the builder

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-07): edits 1–4 required by this review were applied at integration; the integrated index entry is definitionally equal (rfl) to the reviewed Prop. The review text below is unchanged.

Reviewed snapshot: `<builder working folder>/Thm617Wip/` (`diff -r` against `Thm617Wip.reviewed-snapshot`
is empty). Source: `source/upstream/tex/chapters/offlineRL.tex`, sha256 `67cf0d1c…f1e4` (matches provenance).
Key file hashes (sha256):
- `Defs.lean`: `c678e7dacca12482348ac14b4892c62144a844bdde9c3a5ec9b7c6aba9ad6965`
- `StatementDraft.lean`: `77acc94b56915fb0c7bedca7a577cfac626524e0d851a359dd24b2b833f90070`
- `Export.lean`: `07d4c59d699241b4b8ec052178782d7748cf22067212e134f3d954382cf036c7`
- `StatementProof.lean`: `cfe7d48a6dbfd733b591917f45f62caaade024c422b6a5f347c05426a3fa97f9`
- `Theorem.lean`: `53305e612fb94d40fc4c271a60ac0d91cddb9d70008ca5c6c4115220140abbb2`
- `Arith.lean`: `301b6d9e4a2880ebc347c3823cff910166f07c89f441e00b58cd87ade613dfb1`

My files are all in `<reviewer probe folder>/`. I edited nothing else.

## Verdict

**ACCEPT** `Thm6_17_restricted` as an honest restricted entry. There are no blocking findings. Findings 6–9 are
documentation and hygiene edits that the lead makes at integration. The statement matches the printed theorem
binder by binder, apart from the disclosed restriction to one explicit algorithm. The proof compiles from a clean
single-file elaboration of the current sources. The axioms are exactly `propext`, `Classical.choice` and
`Quot.sound`.

## Compile evidence (commands I ran)

All runs were foreground, one Lean process at a time, through `bash scripts/lean-local.sh <file>`, with no `-o`, no
lake and no lean-lsp. No other Lean was running.

| file | exit | wall | result |
|---|---|---|---|
| `<builder working folder>/Thm617Wip/Export.lean` | 0 | 35 s | no errors, no sorry |
| `<builder working folder>/Thm617Wip/StatementProof.lean` | 0 | 19 s | no errors, no sorry |
| `<builder working folder>/AxiomProbe.lean` | 0 | 21 s | both declarations: `[propext, Classical.choice, Quot.sound]` |
| `<reviewer probe folder>/CleanChain.lean` (sha `3509fef5…cb43`) | 0 | 70 s | see below |
| `<reviewer probe folder>/CriticProbe.lean` (sha `f60e161f…9800`) | 0 | — | P1–P3 pass; `output` uses the standard axioms only |

`CleanChain.lean` concatenates all 14 WIP modules in topological order, each wrapped in `section … end`, under one
merged import list. It does not depend on any `Thm617Wip` olean, which makes it the clean end-to-end check (see
finding 8). It also reprints the axioms of `Thm6_17_restricted_holds` and `lcbqFinite_restricted` (standard three
only) and checks `example : Thm6_17_restricted.{0,0,0} := Thm6_17_restricted_holds`. Its single warning is an
unused-section-variable linter warning on `lemmaG`, which comes from my section wrapping.

Grep of the WIP for `sorry|admit|axiom |native_decide|implemented_by|extern`: no hits.

## Source reconstruction (done before reading the draft)

- **Data** (`:2943–2963`): K iid trajectories `s_1~ρ^b`, `a_h~π^b_h`, `s_{h+1}~P_h`. Rewards are known.
- **C⋆** (`:2983–2993`): `max_{s,a,h} d⋆_h(s,a;ρ)/d^b_h(s,a)` with `0/0 = 0`. The text does not say which optimal
  policy defines `d⋆`.
- **Algorithm** (`:3126–3148`):
  - single pass over k;
  - at each h, one update at `(s_h^k,a_h^k)` with target `r + V_{h+1}(s_{h+1}^k) − b_n`;
  - `η_n = (H+1)/(H+n)`, called "a common choice";
  - `b_n = Θ̃(√(H³/n))`, introduced with "for instance";
  - output greedy with respect to `Q^lcb`.
  The initialisation, the V update, the stage order, the tie rule and the log power are not given. The box
  `:3150–3173` is commented out.
- **Theorem 6.17** (`:3176–3192`): for all `δ∈(0,1)`, `ε∈(0,H]` and ρ, with probability at least `1−δ`,
  `V⋆_1(ρ) − V^{π̂}_1(ρ) ≤ ε`, provided `K ≥ c_a H⁵ S C⋆ log³(SAK/δ)/ε²` for some sufficiently large numerical
  `c_a`.

## Findings

### 1. Prop vs printed statement, binder by binder: PASS

| binder / hypothesis | Lean | class | comment |
|---|---|---|---|
| constants | `∃ cb₀>0, ∀ cb ≥ cb₀, ∃ ca>0` | SOURCE (strengthened) | `c_a` is uniform in every instance and in L; any large `c_b` is allowed. This is stronger than the existential reading of Θ̃. |
| S, A | `[Fintype] [Nonempty]` | TYPING | |
| `0 < H` | | DOMAIN | |
| E, πb, ρb, ρ | arbitrary; rewards in [0,1] via `EnvironmentStage` | SOURCE | |
| πs | `∀ πs`, optimal at every (h,s) | STANDING | defines `d⋆`; deterministic π⋆ is disclosed (finding 3). Existence was shown by the 6.16 critic (`exists_isOptimal`). |
| ε, δ | `0<ε≤H`, `0<δ<1` | SOURCE | |
| K | `0 < K` | DOMAIN | disclosed (Lean's `log 0 = 0`) |
| L | `∀ L, ι ≤ L ≤ max(ι, ι³)` | algorithm parameter (restriction) | see finding 2 |
| sel, π₀ | `∀ sel` (maximiser selector), `∀ π₀` | algorithm parameters | universal, so stronger |
| `C⋆ ≠ ⊤` | library ENNReal form | junk guard | `⊤.toReal = 0` would otherwise trivialise the size condition |
| size condition | `ca·H⁵·S·C⋆.toReal·log(SAK/δ)³/ε² ≤ K` | SOURCE | verbatim; `ι = log(SAK/δ)` with the cardinalities and K cast to ℝ |
| data | `Measurable X`, `iIndepFun`, each marginal `= trajMeasure E πb ρb` | SOURCE | same encoding as the accepted `Thm6_16_restricted` |
| conclusion | `1 − δ ≤ μ.real {gap(output) ≤ ε}` | SOURCE | "at least 1−δ", non-strict `≤ ε` |

- No EXCESS hypothesis.
- The parameters L, sel and π₀ are bound before the data X, so the algorithm cannot depend on the data through them.
- The conclusion holds for every optimal deterministic πs whose C⋆ satisfies the condition.
- The C⋆, `optimalValue` and `trajectoryValue` objects are the same library objects as in `Thm6_16_restricted`.

### 2. Widened L range `[ι, max(ι,ι³)]`: HONEST and at least as strong

- Probe P1 proves `ι ≤ L ≤ ι³ → ι ≤ L ≤ max ι ι³` for every real ι. The universal over the widened set therefore
  implies the universal over `[ι, ι³]`.
- The universal over `[ι, ι³]` in turn implies "some penalty `c_b√(H³L/n)` with `L ∈ {ι, ι², ι³}`" (log power
  ≤ 3/2 outside the root, ≤ 3 inside) whenever that set is nonempty.
- Here `ι = log(SAK/δ) > 0` always, since `SAK ≥ 1 > δ`. When `ι ≥ 1` the two ranges coincide.

### 3. Docstring disclosures (CHECK items 1–4 and the brief's list): PASS

`StatementDraft` discloses each of the following:
- the output rule follows `alg:q-infinite-lcb` `:1726–1731` and **departs** from the literal `:3145` reading;
  final-greedy is not proved;
- forward stage order (the box runs backward);
- the penalty is restricted to `c_b√(H³L/n)`, with the upper end ι³ sharp and the lower end proof-driven;
- "any Θ̃ penalty" is false (C33);
- `d⋆` comes from a deterministic π⋆ (a mild restriction);
- `0 < K`, `C⋆ ≠ ⊤`, and the constants `c_b₀ = 5`, `c_a = 10⁶c_b²`.

### 4. `Defs.lean` algorithm fidelity: PASS

`rowStep`, `stagesUpTo`, `episodeStep`, `iterAfter` and `output` implement the plan's completion literally:
- zero Q, V and N, with initial policy π₀;
- episodes `k = 0..K−1`, and within each episode stages `h = 0..H−1` in forward order on
  `(τ.1 (castSucc h), τ.2 h, τ.1 (succ h))`;
- `n = N+1`, `η_n = onlineQRate H n = (H+1)/(H+n)`;
- `b_n = cb·√(H³L/n)`;
- the row update `(1−η)Q + η(r + nextV − b)`, with `nextV = 0` past the last stage;
- monotone `V ← max(V, actionMaximum row)`;
- the policy is changed to `sel row` only when `V_old < v`;
- the output is `.pol` after K episodes.

Junk-value checks:
- The penalty is only evaluated at `n ≥ 1`, so there is no division by zero.
- `L ≥ ι > 0`, so the square root has a nonnegative argument.
- There is no clipping, and Q may go negative, which is legitimate.
- Classical `DecidableEq` in `output` is semantically irrelevant.
- The algorithm reads only `cb`, `L`, `sel`, `π₀`, the rewards and the data.

Probe P3 shows the algorithm is not degenerate: one `rowStep` from `init` with a positive target strictly raises V
and sets the policy to `sel` of the new row.

### 5. Proof spot checks: PASS

- **Constants changed from the plan.**
  - `c_b₀`: 2 → 5. The confidence log is `ι' = log(6HSAK/δ) ≤ 5L`, via `6H·Y ≤ Y⁵` from `Y ≥ 2` and `H ≤ K ≤ Y`.
    The E1 radius needs `4ι' ≤ c_b²L`, i.e. `20L ≤ 25L`. Correct.
  - M1 uses `λ = 1/(2C⋆H²)` with threshold `2C⋆H²ι` (the plan had `1/(C⋆H²)`). This is consistent and gives
    `R = 2HSC⋆ + 8C⋆H²ι' + …`.
  - `final_arith`'s total coefficient is `61/c_a + 840/c_a + 0.48 + 1008c_b/c_a ≤ 1` with `c_a ≥ 2.5·10⁷`. I
    re-derived it by hand.
  - The term-3 bound `2·336²/10⁶ = 0.2258 ≤ 0.48² = 0.2304` holds.
- **Union bound.** `(2HSAK + 2H + HS)·e^{−ι'}`, with `e^{−ι'} = δ/(6HSAK)`, is `≤ δ`, because `2H ≤ 2HSAK` and
  `HS ≤ HSAK`.
- **|A| = 1 corner.** `polV = optV` by induction, so the gap is 0 surely. The export takes
  `Subsingleton A ∨ (L-form size condition)`.
- **`ι < 1` with |A| ≥ 2 corner (in the wrapper).**
  - `SA ≥ 2` gives `ι ≥ log 2 > 0.69`.
  - `ι < 1` gives `SAK/δ < e < 3`, so `K = 1`.
  - Then `ca·H⁵·S·C⋆·ι³/ε² ≤ 1` with `ι³ ≥ 0.3`, `ε ≤ H` and `S·C⋆ ≥ 1` gives `0.3·c_a·H³ ≤ 1`, contradicting
    `c_a ≥ 2.5·10⁷`.
  This is correct, and Lean checks it.
- **Arithmetic non-vacuity** (probe P2). With `c_b = 5`, `c_a = 2.5·10⁷`, `H = S = 1`, `|A| = 2`, `C⋆ = 1`,
  `ε = 1`, `δ = 1/2` and `K = 10¹²`, the printed size condition holds (`log(4·10¹²) ≤ 30`).
  - `C⋆ = 1` is attainable by taking `π^b = π⋆` with full-support `ρ^b = ρ`.
  - iid data exists via the product measure, as in 6.16.
  So the entry is not vacuous in a nontrivial (|A| = 2) case.

### 6. Docstring overstatement on vacuity (minor; edit)

The draft says that when `ι < 1` "only `L = ι` is allowed, so the entry is never vacuous". That is not accurate.
- With |A| ≥ 2 and `ι < 1`, the printed size condition is itself unsatisfiable for these constants (the wrapper
  proves this). Those instances are vacuous for every L, exactly as the printed theorem is.
- The widening only adds content in the trivial |A| = 1 corner.

Reword to: "the L-range is never empty (when `ι < 1` it is `{ι}`); for `|A| ≥ 2` the printed size condition already
forces `ι ≥ 1`".

### 7. Ledger and C33 out of date (edit at integration)

- `docs/SOURCE-ISSUES.md#C33` still says "proof planned for every `ι ≤ L ≤ ι³`" and "No Lean evidence yet". Update it
  to:
  - the proved range `[ι, max(ι,ι³)]`;
  - `c_b₀ = 5`, `c_a = 10⁶c_b²`;
  - the export name.
- C33's sentence "At `a = 3/2` it fails exactly when `c_a < c_b²/32`" overclaims an iff. Only the counterexample
  direction (`c_a < c_b²/32`) is established, and the proof covers `c_a = 10⁶c_b²`. Reword to "the counterexample
  mechanism needs `c_a < c_b²/32`; the restricted proof covers `c_a = 10⁶c_b²`; the gap in between is open".
- Add the COVERAGE row and the PROGRESS ownership note.

### 8. Stale-olean ordering in the WIP build (hygiene; resolved by my clean build)

- `Thm617Wip/Theorem.olean` (16:04:24 local) was compiled before `Arith.olean` was rebuilt from the changed source
  (16:04:33; source sha `301b6d9e…` versus the earlier `166b2ec9…`). `Theorem.olean` therefore elaborated against
  the old `Arith`. It only uses `sqrt_bound`, and `Export` uses the current `final_arith`.
- The concatenated `CleanChain.lean` elaborates every current source from scratch with exit 0 and the standard
  axioms, so the evidence stands.
- At integration, rebuild the library modules in dependency order (`python3 scripts/check.py`). Do not reuse the
  WIP oleans.

### 9. Minor code hygiene (edit at integration)

- `Theorem.lean`'s module docstring names `lcbqFinite_export`. The export is `lcbqFinite_restricted` in
  `Export.lean`.
- Advisory: the wrapper `Thm6_17_restricted_holds` carries about 70 lines of the `ι < 1` corner argument. This is a
  legitimate derivation of the printed form from the export, as AGENTS.md permits, not a second proof. To keep
  `Ch6Proofs.lean` thin, consider moving it into a library lemma, e.g.
  `printed_size_imp_export_size : printed condition → Subsingleton A ∨ L-form condition`.
- `Defs.lean` must land as a definitions-only module (e.g. `Formalization/OfflineRL/LCBQFinite/Definitions.lean`),
  so that `Statements/Ch6.lean` still imports definition modules only.

## Required edits (lead, at integration)

1. Reword the vacuity sentence in the `Thm6_17_restricted` docstring (finding 6).
2. Update C33: the proved range, the constants, the Lean evidence, and the `a = 3/2` iff wording (finding 7). Add the
   COVERAGE and PROGRESS rows.
3. Fix the stale export name in `Theorem.lean`'s docstring (finding 9).
4. Place `Defs` as a definitions-only library module. Rebuild all moved modules in order and run `check.py` plus the
   axiom audit of `Thm6_17_restricted_holds` (finding 8).

There are no changes to the Prop, the algorithm or the proof.
