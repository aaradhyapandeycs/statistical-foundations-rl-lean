# CRITIC: Theorem 6.16 (`thm:finite-VI-LCB`) — WIP `Thm616Wip` / draft `Thm6_16_restricted`

Public copy of the independent critic report; local paths removed.

Post-review note (added to this public copy, 2026-11-07): required edits R1–R3 of this review were addressed in the integration and reviewed in docs/critic-thm6-16-integration.md. The review text below is unchanged.

Independent critic pass (not the builder). Date 2026-11-07. Nothing outside
`<reviewer probe folder>/` and this file was edited.

## Verdict: **ACCEPT WITH DISCLOSURES**

The draft `Prop` is a faithful, self-contained, *stronger-than-printed* statement of Theorem 6.16 for one
explicit, fully defined VI-LCB variant. It compiles, and its axiom closure is clean. Its own value and
occupancy definitions are correct. I proved that they agree with the library's
`EnvironmentStage.optimalValue`, `DecisionStage.trajectoryValue` and `DecisionStage.stateActionOccupancy`
(bridges below, axiom-clean). Integration is conditional on required edits R1–R3. No EXCESS hypothesis
was found, and no source-fidelity defect blocks the `_restricted` entry.

## Pins and evidence

- Source: `chapters/offlineRL.tex` sha256 `67cf0d1c…f1e4` (matches `source/provenance.json`/plan);
  read `:2935–3112`, `:811–822`; `prelim.tex:690–770`.
- WIP files: all 18 `Thm616Wip/*.lean` sha256 match `<builder working folder>/hashes.txt`. `diff -r` against
  `Thm616Wip.reviewed-snapshot` is empty. For every module, the last successful compile hash in
  BUILD-LOG equals the current file hash, and olean mtimes follow the import order. Scan for
  `sorry|admit|axiom |native_decide|implemented_by|opaque|maxHeartbeats|extern|unsafe`: no hits.
- Re-elaborations (critic, `bash scripts/lean-local.sh <file>`, foreground, one at a time, no `-o`):
  - `Thm616Wip/Theorem.lean`: EXIT 0, 69 s, 0 warnings (`<reviewer probe folder>/theorem.out`).
  - `Thm616Wip/StatementDraftProofs.lean`: EXIT 0, 49 s (`proofs.out`).
  - `AxiomProbe.lean`: EXIT 0, 58 s (`axiom.out`). `finite_vilcb_restricted`,
    `tapeMeasure_map_buildMain`, `kept_eq_ideal`, `rows_event`, `Thm6_16_restricted_holds` each depend
    only on `[propext, Classical.choice, Quot.sound]`.
  - Critic probes `<reviewer probe folder>/BridgeProbe.lean` (sha256 `8d409bc6…bda7`, EXIT 0, `bridge.out`) and
    `<reviewer probe folder>/OccupancyProbe.lean` (sha256 `009ec346…618f`, EXIT 0, `occ.out`). All probe
    theorems use only the three standard axioms.

## 1. Independent source reconstruction (before reading the Lean)

∀ ε∈(0,H], δ∈(0,1), ρ∈Δ(S): ∃ VI-LCB variant (backward `Q_h = max{r_h + P̂_h V_{h+1} − b_h, 0}`,
`V_{H+1}=0`, greedy output, Bernstein penalty `Θ̃(√(Var_P̂(V)/N)+H/N)`, refined by "two-fold sample
splitting", `:3061`) and a numerical `c_k>0` such that, for `K` independent trajectories
`s_1~ρ^b, a_h~π^b_h(·|s_h), s_{h+1}~P_h(·|s_h,a_h)` (`:2943–2961`) with `K ≥ c_k H³ S C⋆ log(KH/δ)/ε²`,
`P(V⋆_1(ρ) − V^π̂_1(ρ) ≤ ε) ≥ 1−δ`. Here `C⋆ = max_{s,a,h} d⋆_h(s,a;ρ)/d^b_h(s,a)`, with `0/0=0`
(`:2987–2992`), `d^π_h(s,a;ρ) = P(s_h=s,a_h=a)` (`prelim:751–757`), `V^π_h` is the expected
cumulative reward (`prelim:706–720`), and `V⋆ = V^{π⋆}` for an optimal deterministic π⋆
(`prelim:740–745`). The book gives no proof (C32).

## 2. Binder table (`StatementDraft.lean:38–60`)

| # | Binder | Bin | Note |
|---|---|---|---|
| 1 | `∃ cb₀, 0<cb₀` | SOURCE (Θ̃ constant) | the variant's penalty constant; mirrors `Thm6_3` |
| 2 | `∀ cb ≥ cb₀` | SOURCE | instantiating `cb = 16` gives the printed `∃ variant ∃ c_k` |
| 3 | `∃ ck, 0<ck` | SOURCE (`c_k`) | numerical: chosen before S, A, H, ε, δ, ρ, MDP (`ck = 69120 cb`) |
| 4 | `S A`, `Fintype`, `Nonempty` | TYPING | finite spaces; `EnvironmentStage` already carries nonemptiness |
| 5 | `H`, `0 < H` | TYPING | implied by `0<ε≤H` anyway |
| 6 | `E : Fin H → EnvironmentStage` | STANDING | nonstationary `P_h`, `r_h ∈ [0,1]` (structure fields) |
| 7 | `πb`, `ρb` | SOURCE | behaviour policy and initial law (`:2943`) |
| 8 | `ρ` | SOURCE | test distribution |
| 9 | `πs` + Q⋆-greedy hypothesis | SOURCE (π⋆ in `C⋆`) | ∀ greedy π⋆ is stronger than "the" π⋆. Greedy ⇒ optimal: proved (`isOptimal_attains`) |
| 10 | `ε`, `0<ε`, `ε≤H` | SOURCE | `:3097` |
| 11 | `δ`, `0<δ<1` | SOURCE | |
| 12 | `K`, `0<K` | DOMAIN | `log(KH/δ)` is undefined at K=0. Lean's `log 0 = 0` would make the condition hold and the claim false (plan check 5d). Disclosed |
| 13 | `C⋆ ≠ ⊤` | DOMAIN/TYPING | at `C⋆=∞` the printed condition is unsatisfiable. Needed because `⊤.toReal = 0`. Disclosed |
| 14 | sample condition with `Real.log (K*H/δ)` | SOURCE | `eq:K-complexity-finite`, exact shape |
| 15 | `Ω, μ` probability space | TYPING | |
| 16 | `X : Ω → Fin K → Traj`, `Measurable X`, `iIndepFun`, marginals `= trajMeasure E πb ρb` | SOURCE (data model) | exactly "K independent trajectories" with each law given by eq:finite-batch-size-def. Satisfiable: `data_hyps_satisfiable` (product space) |

Counts: SOURCE 10 (rows 1–3, 7–11, 14, 16), STANDING 1, TYPING 3 (rows 4, 5, 15), DOMAIN 2
(rows 12, 13), RULED 0, **EXCESS 0**.

**Conclusion.** `1−δ ≤ μ.real {ω | ∀ π̂ greedy for qhat(X ω), ρ·optV₀ − ρ·polV(π̂)₀ ≤ ε}`. This is the
printed conclusion for every tie-break, so it is stronger than printed. The set is `X⁻¹` of a subset
of a finite discrete space, hence measurable, so `μ.real` is a genuine probability, not an outer
measure. The algorithm `qhat cb δ r x` receives only `cb`, `δ`, the rewards and the data, never
`P`, `πb`, `ρb`, `ρ`, `ε` or `C⋆`. It is also uniform in ε and ρ, which is stronger than the printed
order.

## 3. Findings

1. **[MAJOR → resolved by critic, integration REQUIRED] Own definitions without library bridges.**
   - Affected definitions: `optV`, `polV` (`Defs.lean:77–91`; Bellman recursions), `occupancy`
     (`Defs.lean:57–60`) and `trajMeasure`/`trajProb` (`:44–54`).
   - The source defines `V^π` as an expectation of cumulative reward (`prelim:706–711`). The Prop
     uses a recursion, so a reader must take the DP identity on trust.
   - Checked by hand: the indices are right (`h ∈ Fin H` is the paper's `h+1`; `s_h = τ.1 h.castSucc`,
     `a_h = τ.2 h`, `s_{h+1} = τ.1 h.succ`; terminal value 0 at `h ≥ H`). `C⋆` is a ⨆ over
     `Fin H × S × A` of `ofReal d⋆ / ofReal d^b` in ℝ≥0∞ (`0/0 = 0`, `x/0 = ⊤`), and `d⋆` uses
     `detPolicy πs` from ρ.
   - Machine-checked bridges, in `<reviewer probe folder>/BridgeProbe.lean` and `OccupancyProbe.lean`:
     - `optV_eq_optimalValue`: `optV E h = optimalValue ((List.ofFn E).drop h)` for all h.
     - `polV_eq_trajectoryValue` / `polV_zero_eq`: `polV E π 0 = trajectoryValue (controlled (List.ofFn E) (extPol π))`.
       This is the actual trajectory-law expectation.
     - `gap_bridge`: the Prop's gap equals the library gap.
     - `isOptimal_attains`: a greedy `πs` attains `optimalValue`. The library's
       `trajectoryValue_le_optimal` then gives that `optV` is the sup over all randomized Markov
       policies, i.e. source V⋆.
     - `occupancy_eq_library`: `occupancy E π ρ h s a = stateActionOccupancy (controlled (List.ofFn E) (extR π)) ρ ⟨h,_⟩ s a`.
   - With these, the definitions are correct. The bridges must still land with the integration (R1).
2. **[MODERATE, docs] C32 process text conflicts.** `docs/SOURCE-ISSUES.md:965–966` says "any formal
   entry must first pin the cited source". li2024settling was never consulted (plan, CHECK, WIP). This
   is acceptable only because the entry is `_restricted` to our own variant and makes no claim about
   li2024settling. C32 must be rewritten to say exactly that (R2). Do not describe the entry as
   "Theorem 6.16" without the restriction.
3. **[MINOR, disclosed] Variant deviations from the sketch `:3040–3056`.**
   - b ≡ 0 at the last stage, from the `‖V̂_{h+1}‖` clip. So the penalty is not literally
     `Θ̃(H/N)` there, nor strictly "decreasing in N".
   - `b = ‖V̂‖` at N = 0.
   - "two-fold splitting" read as aux-determined per-(h,s) first-visit subsampling of the main half.
   - All three are disclosed in the docstring (`StatementDraft.lean:15–31`). They are required, not
     cosmetic: the plan's K = H = 1 analysis shows an `H`-clip fails under ∀-greedy semantics.
   - Algorithm fully explicit and as planned: `trim ι X = ⌊X/4⌋·1{16ι<X}` (`:145`); aux = `k < K/2`;
     `kept` = main, same state, `mainRank < m` (`:168–175`); `normRow` uniform at zero count;
     `vmax = max_s V`.
   - Fine since `V̂ ≥ 0`: `vmax = ‖V‖∞` (`vhatGen_bounds`).
4. **[MINOR] No junk values.**
   - `iota = log(16HK/δ) ≥ 1` (`one_le_iota`).
   - `log(KH/δ) ≥ log 2` in the main branch, and `> 0` always since KH ≥ 1 > δ.
   - Division by `n` only under `n ≠ 0` (`bonus`). `normRow` guards the zero sum.
   - `toReal` is used only under `C⋆ ≠ ⊤`. Since `C⋆ ≥ 1` (`one_le_conc`), the condition is not
     trivialised.
   - The H = 1 branch is a sure, data-free fact (`gap_H_one`, using `bonus_zero`). It is not
     vacuous: H = 1 is a genuine case.
5. **[INFO] Proof spot checks (all compiled, axiom-clean).**
   - Lemma T, `tapeMeasure_map_buildMain` (`TapeLaw.lean:238`): the pushforward of an honest product
     `initMeasure × actMeasure × samplingLaw` equals `Measure.pi trajMeasure`, via singleton
     computation.
   - `data_transfer` (`Prelim.lean:42`) uses `iIndepFun_iff_map_fun_eq_pi_map` plus `hlaw`.
     Independence and the law are genuinely consumed.
   - `kept_eq_ideal` / `qhat_eq_ideal` hold on the trim event, which follows from E1 ∧ E2
     (`trim_of_events`).
   - Budget: E1, E2, E3, E4 each `≤ HS e^{-ι} ≤ δ/16`, using `S ≤ K`. E5 `≤ 8δ'·|visited| ≤ 8·δ/(4HK)·HK/8 = δ/4`.
     Total δ/2 ≤ δ (`Theorem.lean:221–296`).
   - `S ≤ K` (`:134–152`) uses `C⋆ ≥ 1`, `cb ≥ 16`, `log(KH/δ) ≥ log 2 > 0.69`, `ε ≤ H`, giving
     `69120·cb·C·log ≥ 1`.
   - Final constant `ck = 69120 cb` (`final_arith`, `hHY`). `ι ≤ 5 log(KH/δ)` needs `HK ≥ 2`
     (main branch only).
6. **[MINOR] Non-vacuity.**
   - `data_hyps_satisfiable`: `Measure.pi`, `id` satisfy every data hypothesis for every K.
   - `conc_self_le_one`: `C⋆ ≤ 1 < ⊤` when `πb = detPolicy πs`, `ρb = ρ`. Since `log K` grows
     sublinearly, the sample condition holds for large K. Every hypothesis is therefore jointly
     satisfiable.
7. **[MINOR] Converse of the π⋆ hypothesis is not formalised.** A policy optimal at every (h,s)
   (the source's π⋆, `prelim:740`) is Q⋆-greedy. This is a one-line consequence of `optV`'s
   definition, not proved here. Since the Prop quantifies ∀ greedy πs, it covers the source π⋆ only
   through this standard fact. A small lemma or a docstring sentence suffices (R3).
8. **[MINOR, hygiene]** `Defs.lean` (imported by the definitions-only Statement file) also holds
   analysis-only tape definitions (`ActTape`…`idealNext`, `:195–255`). On integration, move them to a
   proof-side module so the Statement imports only algorithm, model and definition objects.

## 4. Required edits (before integration)

- **R1 (REQUIRED).** Land the bridge lemmas (`optV_eq_optimalValue`, `polV_eq_trajectoryValue`,
  `gap_bridge`, `isOptimal_attains`, `occupancy_eq_library`, plus `controlled_length`,
  `controlled_getElem`, `stateAfter_append_single`, `stateMarg_eq_stateAfter`) in a library module,
  e.g. `Formalization/OfflineRL/FiniteVILCB/LibraryBridge.lean`.
  - Preferred: restate the index entry over the library objects: `EnvironmentStage.optimalValue (List.ofFn E)`,
    `DecisionStage.trajectoryValue (controlled (List.ofFn E) (extPol π̂))`, and `C⋆` via
    `stateActionOccupancy`. Derive it in `Ch6Proofs` from `finite_vilcb_restricted` and the bridges.
    The library theorem signature does not change.
  - Minimum: keep the Prop and cite the bridges in its docstring.
- **R2 (REQUIRED).** Update `docs/SOURCE-ISSUES.md#C32`: "restricted variant proved (our
  reconstruction; li2024settling not pinned or consulted; no claim about its algorithm or constants)".
  List the domain premises `0<K` and `C⋆≠⊤` and the variant deviations in Finding 3. Update
  COVERAGE/PROGRESS in the same change as the index entry (AGENTS.md).
- **R3 (recommended).** Add the "optimal at all (h,s) ⇒ greedy" lemma or a docstring note (Finding 7).
  Split the tape definitions out of `Defs.lean` (Finding 8). Delete the WIP oleans
  `.lake/build/lib/lean/Thm616Wip/*` after integration.
- Re-run `python3 scripts/check.py` / the axiom audit on the integrated tree. The evidence here covers
  only the WIP tree.
