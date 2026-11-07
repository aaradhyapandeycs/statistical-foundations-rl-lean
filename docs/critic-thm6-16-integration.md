# CRITIC: integration of restricted Theorem 6.16 (`thm:finite-VI-LCB`)

Public copy of the independent critic report; local paths removed.

Independent critic (not the builder). Date 2026-11-07. I edited nothing outside
`<reviewer probe folder>/` and this file.

## Verdict: **ACCEPT** (no blocking findings; three optional docstring/hygiene edits)

`Thm6_16_restricted` is now stated over the library objects `EnvironmentStage.optimalValue`,
`DecisionStage.trajectoryValue` and `DecisionStage.stateActionOccupancy`. It still matches the
printed statement binder by binder. The bridges and the converse are genuine. The wrapper only
applies the unchanged export `finite_vilcb_restricted` through the bridges. Everything compiles,
the axiom closure is clean, and the project-wide audit passes. R1 and R3 of `docs/critic-thm6-16.md`
are met. R2 is met in substance, with one optional addition (O3).

## Pins and evidence

- Source: `chapters/offlineRL.tex` sha256 `67cf0d1c…f1e4` and `chapters/prelim.tex` sha256
  `2d27bb72…31a5`. I re-read `:2943–2993`, `:3055–3062` and `:3093–3112`, and `prelim:700–757`.
- Module diff against the reviewed snapshot:
  - Comparing `Thm616Wip.reviewed-snapshot/*.lean` with `Formalization/OfflineRL/FiniteVILCB/*.lean`,
    the 15 shared modules differ only in their `import` lines. `Theorem.lean` also differs in one
    docstring word (`Thm616Wip.Defs` → `FiniteVILCB.Definitions`). `CountTails` is identical.
  - `Definitions.lean` equals the old `Defs.lean` with these changes:
    - the `section Tapes` block is removed;
    - imports are adjusted (`FiniteHorizonSamplingDefinitions` moved out; added
      `PolicyEnvironmentDefinitions` and `BigOperators.Field`);
    - one docstring line is changed;
    - three declarations are added: `extPolicy`, `controlled_length` and `stageIndex`.
  - `TapeDefinitions.lean` has `section Tapes … end Tapes` byte-identical to the old block. It uses
    the same `Classical.decEq` local instances.
  - No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `maxHeartbeats`,
    `unsafe` or `extern` appears, and there are no private paths.
- Olean freshness: for all 18 modules plus `Statements/Ch6.lean`, `Ch6Proofs.lean` and
  `Formalization.lean`, the current sha256 prefix equals the last EXIT-0 entry in
  `<builder working folder>/BUILD-LOG.md`, and each olean mtime is later than its source mtime. The WIP oleans
  `.lake/build/lib/lean/Thm616Wip/` are gone, and nothing references `Thm616Wip`.
- My runs used `bash scripts/lean-local.sh <file>`, foreground, one at a time, without `-o`:

  | File | Result | Time | Output | Shows |
  |---|---|---|---|---|
  | `<builder working folder>/IntegrationProbe.lean` | EXIT 0 | 51 s | `<reviewer probe folder>/integration-probe.out` | `Iff.rfl` and the `type_of% … = Thm6_16_restricted` rfl check pass. `Thm6_16_restricted_holds`, `finite_vilcb_restricted`, `isOptimal_of_optimal`, `concentrability_eq_library`, `gap_bridge`, `occupancy_eq_library` and `tapeMeasure_map_buildMain` all depend only on `[propext, Classical.choice, Quot.sound]` |
  | `<reviewer probe folder>/CriticProbe.lean` (sha256 `9b2ebc55…2332`) | EXIT 0 | 65 s | `probe.out` | see the list below; one unused-section-variable linter warning only |
  | `Audit.lean` | EXIT 0 | 92 s | `<reviewer probe folder>/audit.out` | "Axiom audit passed for 12603 project declarations." |

  `CriticProbe.lean` machine-checks the following:
  - (a) `ofReal (1/2) / ofReal 0 = ⊤` and `ofReal 0 / ofReal 0 = 0`.
  - (e) `extPolicy π h.val = π h`.
  - (b) `entryOpt_of_isOptimal`: Q⋆-greedy ⇒ the entry's π⋆ hypothesis. Together with the builder's
    `isOptimal_of_optimal`, the entry's π⋆ class equals the Q⋆-greedy class.
  - (c) `exists_isOptimal`: the π⋆ hypothesis is satisfiable.
  - (d) The entry's π⋆ dominates every randomized Markov policy `π : ℕ → StationaryPolicy`
    (via `EnvironmentStage.trajectoryValue_le_optimal`). So `optimalValue (List.ofFn E)` is the
    source's `V⋆` (a supremum over policies).
  - All new probe theorems depend only on the three standard axioms.
- I did not run `python3 scripts/check.py` in full. The equivalent axiom audit above passed on the
  builder's oleans, whose hashes I verified.

## 1. Binder-by-binder check of the restated entry (`Statements/Ch6.lean`, section FiniteVILCBTheorem)

| Binder | Status |
|---|---|
| `∃ cb₀>0 ∀ cb≥cb₀ ∃ ck>0` | Unchanged from the reviewed draft. It is at least the printed "∃ variant ∃ c_k" (instantiate cb = 16). |
| `S A` Fintype/Nonempty, `0<H`, `E`, `πb`, `ρb`, `ρ` | Unchanged. These are TYPING/STANDING binders; `0<H` is implied by `0<ε≤H`. |
| `πs` + hypothesis "trajectoryValue on every suffix = optimalValue of that suffix, ∀ h s" | **Changed from "Q⋆-greedy" (draft).** It encodes `prelim:740–745` (π⋆ simultaneously maximizes `V_h` for all h, s). It is equivalent to Q⋆-greedy (both directions machine-checked: `isOptimal_of_optimal`, probe `entryOpt_of_isOptimal`). It is satisfiable (probe c). Because `optimalValue` dominates every Markov policy (probe d), it is exactly the source's set of optimal deterministic policies. Since the entry quantifies ∀ over this set, it is at least as strong as the printed statement. The shift `fun j ↦ extPolicy … (h + j)` is correct: `controlled` reads `π 0` for the head and shifts for the tail, so the suffix from `h` uses `πs h, πs (h+1), …`. |
| `ε, δ` ranges, `0<K` | Unchanged. `0<K` is a disclosed domain condition. |
| `Cstar` | `⨆ h s a, ofReal d⋆ / ofReal d^b` in ℝ≥0∞. This is a **ratio of `ofReal`s**, not `ofReal` of a real ratio, so no junk value arises: `x/0 = ⊤` for `x>0` and `0/0 = 0` (probe a). Occupancies are ≥ 0, so `ofReal` is lossless. `d⋆` uses `extPolicy (detPolicy πs)` from `ρ`; `d^b` uses `extPolicy πb` from `ρb` (`eq:dhb-finite`). The index `stageIndex … h` is `h.val`, the paper's `h+1`, and `stateActionOccupancy` takes the first `h` stages and then stage `h` (`eq:dh-pi-defn`). `concentrability_eq_library` proves it equal to the reviewed WIP `concentrability` by `simp only [occupancy_eq_library]`. This matches the source's `0/0 = 0` (`:2992`). At `x/0` the source is silent; `∞` is the only reading under which the printed `max` is meaningful, and `C⋆ ≠ ⊤` is a disclosed premise. |
| `Cstar ≠ ⊤`, sample condition `ck·H³·card S·C⋆.toReal·log(KH/δ)/ε² ≤ K` | Same shape as `eq:K-complexity-finite`. |
| `Ω, μ, X`, measurability, `iIndepFun`, marginal law `trajMeasure E πb ρb` | Unchanged. The data law is still the project's own `trajProb` product formula, a direct transcription of `eq:finite-batch-size-def`. The docstring discloses this ("law `FiniteVILCB.trajMeasure`"). It was not part of R1. |
| Conclusion | `ρ·optimalValue(List.ofFn E) − ρ·trajectoryValue(controlled (List.ofFn E) (extPolicy (detPolicy π̂))) ≤ ε` for every greedy π̂. This is `V⋆_1(ρ) − V^π̂_1(ρ)` with `V^π` as the expectation of cumulative reward under the trajectory law (`prelim:706–720`), and the terminal value is 0 (`optimalValue [] = 0`, `trajectoryValue [] = 0`). |

No new hypothesis was introduced. EXCESS count: 0.

**`extPolicy`.** For `n < H` it is `π ⟨n,_⟩` (probe e). For `n ≥ H` it is a point mass at an
arbitrary action. `controlled (List.ofFn E)` has length H (`controlled_length`) and reads only
indices `< H`, so the junk tail is never consulted. On the suffix lists in the π⋆ hypothesis the
indices are `h+j < H`. It is a faithful extension.

## 2. Bridges and converse

All bridges are genuine. They are proved by structural induction on suffix length or by
`simp only` with a proved lemma; none is a definitional restatement and none adds a hypothesis.

- `optV_eq_optimalValue` and `polV_eq_trajectoryValue` hold for every suffix, not only for h = 0.
- `polV_eq_trajectoryValue` goes through `trajectoryValue_cons`, so it is the expectation over the
  actual trajectory law.
- `gap_bridge` is a rewrite by `optV_zero_eq` and `polV_zero_eq`.
- `occupancy_eq_library` goes through `stateMarg_eq_stateAfter`, `controlled_getElem` and the
  library's `stateActionOccupancy_eq`.
- `concentrability_eq_library` is `simp only [occupancy_eq_library]` applied pointwise.
- `isOptimal_of_optimal` takes exactly the entry's hypothesis (syntactically identical) and
  derives `IsOptimal` using `le_actionMaximum` on `optV`. It is genuine.
- The wrapper `Thm6_16_restricted_holds`:
  1. rewrites `Cstar` to the old `concentrability`;
  2. applies `finite_vilcb_restricted` (signature unchanged from the reviewed snapshot) with
     `isOptimal_of_optimal`;
  3. finishes by `simp only [gap_bridge]`.

  It contains no second proof.

## 3. Disclosures (docstring of `Thm6_16_restricted`)

The following are present and accurate:
- the `_restricted` variant and the absence of any claim about li2024settling;
- the two-fold split and the reading of `:3061` as ours;
- the backward recursion and indexing;
- the penalty clipped at `‖V̂_{h+1}‖`, giving `b ≡ 0` at the last stage, which is not literally
  `Θ̃(H/N)` and not strictly decreasing;
- `‖V̂‖` at zero count and the uniform row at zero count;
- every greedy output;
- the algorithm's inputs;
- `c_b₀ = 16` and `c_k = 69120 c_b`;
- `0<K` with the reason (`log 0 = 0`);
- `C⋆` in ℝ≥0∞ with `0/0 = 0` and `C⋆ ≠ ⊤` essential (`⊤.toReal = 0`);
- the π⋆ reading (`prelim.tex:740–745`);
- the library objects for `V⋆` and `V^π̂`;
- the data model and its law.

The `.tex` range `:3093–3112` is correct. `docs/SOURCE-ISSUES.md#C32` and `docs/COVERAGE.md`
state the restriction, the domain conditions and the library objects.

## 4. Findings

1. **[INFO]** The data law (`trajMeasure`/`trajProb`) is the only remaining project-own object in
   the statement. It is an explicit product formula transcribing `eq:finite-batch-size-def`, and
   it is disclosed. Acceptable.
2. **[MINOR, hygiene]** `Statements/Ch6.lean` now imports `Formalization.MDP.FiniteOccupancy`, which
   holds proofs. The only `stateActionOccupancy` lives there, and the file already imports the
   non-Definitions modules `MDP.DiscountedOccupancy` and `MDP.OptimalTrajectoryValue` (precedent).
   `Definitions.lean` contains one small theorem, `controlled_length`, which `stageIndex` needs.
   Neither is a fidelity issue.
3. **[MINOR, docs]** The docstring gives `0/0 = 0` but does not say that `x/0 = ∞` for `x>0`. That
   is the reading under which the premise `C⋆ ≠ ⊤` carries content (the `Definitions.lean`
   docstring of `concentrability` does say it).
4. **[MINOR, docs]** The π⋆ hypothesis compares with the DP value `optimalValue`. The fact that
   this equals the source's supremum over policies rests on the library's
   `trajectoryValue_le_optimal`. A docstring pointer would let a reader check this without opening
   proofs.
5. **[PROCESS]** The working-tree diff of `docs/SOURCE-ISSUES.md` also rewrites **C33** (Theorem 6.17
   classification). That edit is unrelated to this integration and not reviewed here. The lead
   should land it separately or with its own review. C32's wording "Independently plan-checked and
   source-reviewed" is accurate once this review is accepted.

## 5. Required edits

None are blocking. The following are optional:

- **O1.** In the `Thm6_16_restricted` docstring, change "(`0/0 = 0`)" to "(`0/0 = 0`, `x/0 = ∞` for
  `x > 0`)".
- **O2.** Add to the π⋆ bullet: "`optimalValue` dominates every randomized Markov policy
  (`EnvironmentStage.trajectoryValue_le_optimal`), so this is the source's optimality; the
  hypothesis is equivalent to Q⋆-greediness (`FiniteVILCB.isOptimal_of_optimal`)."
- **O3.** C32 could also list "penalty `‖V̂_{h+1}‖` at zero count" among the variant deviations
  (the docstring already has it).
- Before committing, keep the unrelated C33 edit out of this change or have it reviewed (Finding 5).
  Run `python3 scripts/check.py` once on the final tree if any further edit is made. Any docstring
  edit requires recompiling `Ch6.lean`, `Ch6Proofs.lean`, `Formalization.lean` and `Audit.lean`.
