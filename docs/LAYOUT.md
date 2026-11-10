# Library layout

This file maps the Lean library's directories to the book. It is not a status claim: which results are
proved, corrected, restricted or refuted is recorded only in [COVERAGE.md](COVERAGE.md),
[named-result-status.json](named-result-status.json) and [SOURCE-ISSUES.md](SOURCE-ISSUES.md). The formalization
is incomplete.

Counts below were measured on 2026-11-10 (1,514 `.lean` files under `Formalization/`, after the Option A move). The tree is moving, so
re-measure before you rely on a number:

```sh
find Formalization -name '*.lean' | xargs -n1 dirname | sort | uniq -c
```

## 1. Conventions

- **Module paths and namespaces are independent.** A declaration's name comes from its `namespace` lines, not
  from its file path. The ledger, the statement index, COVERAGE and the review records cite declaration names,
  so moving a file changes only its module name (`import` lines). For example,
  `Formalization/MultiAgent/ModelBased/Definitions.lean` (formerly `Ch7Rest/Marl76Defs.lean`) declares names in
  `StatisticalRL.Ch7Rest.Marl76`, and they keep those names after the move; likewise `RobustRL/LowerBounds/*` still
  declares `StatisticalRL.RobustRL.Ch7.*`. Namespace renames are
  out of scope for layout work (they would change cited names; see §5).
- **Every declaration is under `namespace StatisticalRL…`.** `Audit.lean` audits axioms only for names with
  that prefix (static gate G6).
- **Statement index.** `Formalization/Statements/ChN.lean` holds one `Prop`-valued entry per proved source
  result (`def Thm3_2 : Prop := …`), with the source label and `.tex` line range in its docstring. `ChN.lean`
  imports definition modules only (frozen allowlist `scripts/gates/g2_statement_imports.txt`) and never a
  `*Proofs` module. `ChNProofs.lean` imports `ChN.lean` and the proof modules and proves each entry
  (`theorem Thm3_2_holds : Thm3_2 := …`) by applying the existing library theorem. Both are imported from
  `Formalization.lean`.
- **Statements files are located by path.** The site reader finds the index with the pattern
  `Statements/Ch\d+.lean` and the proofs file by replacing `.lean` with `Proofs.lean`. Library exports are found by
  declaration name and namespace. So library files may move; Statements files must not
  (`scripts/move_modules.py` refuses).
- Namespace quirks, kept as is: Ch2 and Ch5 entries use `StatisticalRL.Statements`; Ch3, Ch4, Ch6 and Ch7 use
  `StatisticalRL.Statements.ChN`. `Statements/QLearningProofs.lean` is a one-line legacy shim
  (`import Formalization.Statements.Ch5Proofs`). The former library module `Statements/Ch3Definitions.lean` now lives at
  `Generative/ModelBasedDefinitions.lean`, so no library module imports `Statements/` and
  `scripts/gates/g2_library_to_statements.txt` is empty (header only).
- **New files.** Descriptive file names; theorem numbers go in the module docstring, not the file name
  (exception: a printed-statement or refutation file may keep the number when two results share a directory).
  Use the `Definitions` suffix for definition-only modules. Start with a `/-! … -/` module docstring that cites the
  source label and `.tex` lines. Import specific Mathlib modules, not bare `import Mathlib` (frozen allowlist
  `scripts/gates/g2_bare_mathlib.txt`).
- **Layers** (intended import direction): 0 `Analysis/`, `PrelimKL/`, `Probability/` → 1 `MDP/` → 2 chapter
  directories → 3 `Statements/`. Only two kinds of edge are gated today: imports of `Statements/ChN.lean`
  (`g2_statement_imports.txt`) and library → `Statements` imports (`g2_library_to_statements.txt`, now empty). No gate checks
  layer-0 → `MDP/` or layer-0/`MDP/` → chapter imports. The remaining upward edges are listed in §3.1 as debt.

## 2. Current directories

| Directory | Files | Book chapter / section | Main namespaces |
| --- | ---: | --- | --- |
| `Analysis/` | 12 | Ch2 contraction; step-size sums for Ch4 and Ch7 TD; resolvent series; Taylor bounds | `StatisticalRL`, `.Analysis`, `.Probability` |
| `PrelimKL/` | 7 | Ch2 KL facts (chain rule, products) | `.PrelimKL` |
| `Probability/` (root) | 81 | Ch2 concentration (Hoeffding, Bernstein, Freedman, Azuma), variance, Gaussian tools, `ConvexDistanceTV`, `GaussianSubgaussian` | `.FiniteDistribution`, `.Probability`, `StatisticalRL` |
| `Probability/EmpiricalBernsteinSharp/` | 43 | Ch2 sharp empirical Bernstein | `.EmpiricalBernsteinEntropy` |
| `Probability/Fano/` | 12 | Ch2 Fano (Lemma 2.10), finite-partition KL | `.PrelimFano` |
| `Probability/FiniteMarkov/` | 5 | Ch4 Theorem 4.12 support | |
| `Probability/InformationTheory/` | 4 | generic Pinsker, countable L1/tail-log-sum and stopped-prefix TV lemmas (from `ModelFree/QLearning*`) | |
| `MDP/` | 44 | Ch2 MDP basics shared by all chapters (`FiniteDistribution` is in `CoreDefinitions`) | `.DiscountedMDP`, `.DecisionStage`, `.EnvironmentStage` |
| `Generative/` | 158 | Ch3 model-based generative model (incl. `ModelBasedDefinitions`); `GenerativeLowerBound*` lower-bound machinery used by Fano | `.GenerativeLowerBound`, `.ModelBasedPolicy{Evaluation,Learning}`, `.FiniteHorizonGenerative` |
| `Obstructions/` | 9 | Ch3 Theorem 3.7 obstructions (`HardMDP`, singleton action) | `.Obstructions` |
| `ModelFree/` (root) | 183 | Ch4 TD and Q-learning (upper and lower bounds) | `.QLearning`, `.TemporalDifference` |
| `ModelFree/AsyncQ/` | 11 | Ch4 Theorem 4.12 (asynchronous Q-learning) | `.AsyncQ` |
| `ModelFree/FiniteQ/` | 12 | Ch4 Theorem 4.13 (finite horizon) | `.FiniteQLearning` |
| `Online/` (34 subdirectories) | 626 | Ch5 online RL: bandits §5.2 (`Bandit/`), UCBVI regret (`Regret/T*`, `W*`), MVP (`Regret/MVP/`), UCB-Q (`QLearning/`), lower bounds (`LowerBound/`), regret-to-PAC; `Regret/Algebra/` holds the five Ch5 algebra modules moved out of `Probability/`; `Hedge/` is reused by Ch7 Theorem 7.7 | `.OnlineRL`, `.Bandit`, `.OnlineLowerBound`, `.FiniteHorizonGenerative` |
| `Counterexamples/` | 3 | Ch5 Lemma 5.13 and a variance counterexample | `.SourceCounterexamples` |
| `OfflineRL/` (root) | 55 | Ch6 offline RL | `.OfflineRL`, `.OfflineVILCB` |
| `OfflineRL/FiniteLCBQ/` | 12 | Ch6 LCB-Q, finite horizon | `.LCBQFinite` |
| `OfflineRL/FiniteVILCB/` | 18 | Ch6 VI-LCB, finite horizon | `.FiniteVILCB` |
| `RobustRL/` (root) | 34 | Ch7 §7.1 robust RL: TV and χ² duality | `.RobustRL` |
| `RobustRL/DRVI/` | 31 | Ch7 §7.1 DRVI upper bounds (Theorems 7.2, 7.4) and robust Q-optimality | `.RobustRL` |
| `RobustRL/LowerBounds/` | 17 | Ch7 §7.1 lower bounds (Theorems 7.3, 7.5, randomized), printed statements, horizon-trap refutation of 7.2/7.4 | `.RobustRL.Ch7.*` |
| `MultiAgent/` (`ModelBased/`, `Hedge/`, `LowerBound/`) | 40 | Ch7 §7.2 multi-agent: Theorem 7.6, 7.7, 7.8, `NearSupersolution`, `Equilibria` | `.Ch7Rest.{Marl,Marl76,Marl77}` |
| `Federated/` (`Sync/`, `LowerBound/`) | 11 | Ch7 §7.3 federated: Theorem 7.9 (`Sync/`), 7.10 (`LowerBound/`) | `.Ch7Rest.{FedSync,Fed,FedGeneric}` |
| `TDInference/` (`ConvexSets/`, `Confidence/`, `PluginCovariance/`) | 55 | Ch7 §7.4 TD inference (Theorem 7.11) | `.Ch7Rest.TDInference` |
| `RLHF/VPO/` | 16 | Ch7 §7.5 RLHF (Theorem 7.12) | `.Ch7Rest.Rlhf` |
| `Statements/` | 15 | Statement index Ch1–Ch7 and their `*Proofs`, `QLearningProofs` shim | `.Statements`, `.Statements.ChN` |

Known inconsistencies: Chapter 7 is split over `RobustRL/`, `MultiAgent/`, `Federated/`, `TDInference/` and `RLHF/`;
module paths and namespaces now differ for Chapter 7 (`StatisticalRL.Ch7Rest.*`, `StatisticalRL.RobustRL.Ch7.*` live on); theorem numbers
appear in some file names (`LowerBound73Values`, `LowerBound75`), sometimes as prefix and sometimes as
suffix; `Defs` and `Definitions` suffixes are both used; some generic modules live in chapter directories and some
chapter-specific modules live in `Probability/`.

## 3. Layout (Option A, applied 2026-11-10)

Option A kept `RobustRL/` in place, renamed `RobustRL/Ch7/` to `RobustRL/LowerBounds/`, split `Ch7Rest/` into
four top-level directories, and moved a few clean generic modules. `Ch7Rest/` and `RobustRL/Ch7/` no longer exist. Only module paths change; file contents change
only in `import` lines; namespaces and declaration names stay the same. The full old → new table is
[layout-moves.json](layout-moves.json) (152 entries, status `applied`).

```
Formalization/
  Analysis/  PrelimKL/  Probability/{,EmpiricalBernsteinSharp,Fano,FiniteMarkov,InformationTheory}/   layer 0
  MDP/                                                                                          layer 1
  Generative/  Obstructions/  ModelFree/  Online/  Counterexamples/  OfflineRL/                 layer 2 (Ch3–Ch6)
  RobustRL/{,DRVI,LowerBounds}/                                                                 layer 2 (Ch7 §7.1)
  MultiAgent/{ModelBased,Hedge,LowerBound}/  + NearSupersolution.lean                          layer 2 (Ch7 §7.2)
  Federated/{Sync,LowerBound}/                                                                  layer 2 (Ch7 §7.3)
  TDInference/{,ConvexSets,Confidence,PluginCovariance}/                                         layer 2 (Ch7 §7.4)
  RLHF/VPO/                                                                                     layer 2 (Ch7 §7.5)
  Statements/ChN.lean, ChNProofs.lean (paths unchanged)                                         layer 3
```

| Group in `layout-moves.json` | Moves | From → to |
| --- | ---: | --- |
| `ch7-multiagent` | 40 | `Ch7Rest/Marl76*` → `MultiAgent/ModelBased/` (Theorem 7.6; `Marl76ZeroSumNEOracle` → `ZeroSumNEOracle`), `Marl77*` → `MultiAgent/Hedge/` (Theorem 7.7; the witness is optimistic Hedge), `Marl78*`, `MarlPrinted78`, `SingletonAction78` → `MultiAgent/LowerBound/` (Theorem 7.8), `MarlNearSupersolution` → `MultiAgent/NearSupersolution`, `MarlBestResponse` → `MultiAgent/Equilibria` |
| `ch7-federated` | 11 | `FedSync79*`, `FedPrinted79`, `LargeStep79` → `Federated/Sync/` (Theorem 7.9); `FedGeneric710`, `LowerBound710`, `InnerConstant710` → `Federated/LowerBound/` (Theorem 7.10) |
| `ch7-td-inference` | 55 | `TDInference*711` → `TDInference/` (Theorem 7.11); `TDInferenceConvex*711` → `TDInference/ConvexSets/`, `TDInferenceConf*711` and `TDInferenceC47*711` → `TDInference/Confidence/`, `TDInferencePlugin*711` → `TDInference/PluginCovariance/` |
| `ch7-rlhf` | 16 | `VPO*712`, `RlhfPrinted712` → `RLHF/VPO/` (Theorem 7.12) |
| `ch7-robust-lower-bounds` | 17 | `RobustRL/Ch7/*` → `RobustRL/LowerBounds/*` (same file names; includes the horizon-trap refutation of 7.2/7.4, the printed-statement definitions and `RandomizedLowerBound`) |
| `generic-to-probability` | 6 | `ModelFree/QLearning{PinskerBinary,CountableL1Difference,CountableTailLogSum,StoppedPrefixPayoffTV}` → `Probability/InformationTheory/`; `OfflineRL/GaussianSubgaussian` and `Ch7Rest/ConvexDistanceTV711` → `Probability/` |
| `generic-to-mdp` | 1 | `Online/SourceOptimism/FinitePathHistoryDefinitions` → `MDP/` (removes the `MDP/FiniteTrajectory` → `Online` edges) |
| `chapter-specific-out-of-probability` | 5 | `Probability/Online{T234ConfidenceAlgebra,T56ConfidenceAlgebra,T56RadiusBridge,T56ScalarAlgebra,VarianceRadiusAlgebra}` → `Online/Regret/Algebra/` (removes the `Probability` → `Online` edge) |
| `statements-definitions-out` | 1 | `Statements/Ch3Definitions` → `Generative/ModelBasedDefinitions` (map flag `allow_statements_source`; removes all 17 library → `Statements` imports) |

A generic move was proposed only when the module's whole import closure already lies in `Analysis/`,
`PrelimKL/`, `Probability/` and Mathlib (or `MDP/` for the MDP move), so the move cannot create a new upward edge.

Considered and not proposed:

- `Generative/GenerativeLowerBound{FiniteDataProcessing,FiniteKLDataProcessing,WeightedLog,AffinityOverlap}` →
  `Probability/InformationTheory/`. Each of these imports (transitively) `Generative/PolicyEvaluationSampleAssembly`,
  `ModelBasedPolicyEvaluation` and about 30 `MDP/` modules. Moving them would only rename the
  `Probability/Fano` → `Generative` edge into a `Probability` → `Generative` edge. Fixing it needs content edits
  (narrower imports or splitting files), so it is outside a pure move.
- Generic declarations that live inside chapter files (`StatisticalRL.Fintype.sum_fin_succ_snoc`,
  `abs_apply_le_norm`, `prob_le_one`, …). Moving a declaration between files edits file contents, so it is not a
  module move. See §4.
- `MultiAgent/ModelBased/StageCCE` (CCE existence for finite normal-form games), `TDInference/StepSize` and
  `TDInference/PathMarginals` are generic in content but import chapter modules, so they move with their
  chapter.

### 3.1 Upward import edges (documented debt, not gated)

Before the move there were 34 upward edges by the full-closure checker (`.local` import check); the move removed 20 of
them (2 × `MDP` → `Online`, `Probability` → `Online`, 17 × library → `Statements.Ch3Definitions`) and added none.
14 remain (post-move module names):

| From (layer) | To | Edge |
| --- | --- | --- |
| `Analysis/` (0) | `MDP/` | `Analysis.StochasticResolventSeries` → `MDP.CoreDefinitions` |
| `Probability/` (0) | `MDP/` | `Probability.AdaptiveKLDefinitions` → `MDP.CoreDefinitions` |
| | | `Probability.FiniteSampleDefinitions` → `MDP.CoreDefinitions` |
| | | `Probability.VarianceDefinitions` → `MDP.CoreDefinitions` |
| | | `Probability.Variance` → `MDP.Basic` |
| | | `Probability.EmpiricalRow` → `MDP.InfiniteTrajectory` |
| `Probability/` (0) | `Generative/` (2) | `Probability.AdaptiveKL` → `Generative.GenerativeLowerBoundFiniteKLDataProcessing` |
| | | `Probability.Fano.FanoLemma` → `Generative.GenerativeLowerBound{FiniteDataProcessing,FiniteKLDataProcessing,WeightedLog,AffinityOverlap}` (4 edges) |
| | | `Probability.Fano.FinitePartitionKL` → `Generative.GenerativeLowerBoundFiniteKLDataProcessing` |
| `Probability/` (0) | `TDInference/` (2) | `Probability.GaussianCovCompare` → `TDInference.{Definitions,SmoothApproximation}` (2 edges; pre-existing as `→ Ch7Rest.*`) |

Most of the `MDP/CoreDefinitions` edges exist because `FiniteDistribution` lives there. Removing any of these
edges needs content edits (narrower imports, splitting a file, or moving `FiniteDistribution`), so they are out of
scope for a pure move. A layering gate would freeze this list and let it only shrink.

## 4. Known duplicates (documented debt)

The declarations below have the same short name in different namespaces, so nothing clashes and every copy is
proved. They are maintenance debt, not correctness issues. Policy: do not delete or rewrite them during layout
work. New code should use one canonical lemma (Mathlib's when one exists). Replacing a duplicate with a delegation
or a `@[deprecated] alias` is a proof-content change and needs lead approval, one namespace per change. Line
numbers are from 2026-11-08.

| Name | Copies (file:line) | Canonical replacement |
| --- | --- | --- |
| `prob_le_one` (`p.prob x ≤ 1` for `FiniteDistribution`) | `MultiAgent/Hedge/StageBounds.lean:100`, `TDInference/Noise.lean:339`, `OfflineRL/FiniteVILCB/Links.lean:136`, `Online/LowerBound/ValueGap.lean:40`; also `MDP/DiscountedOccupancy.lean:47` `finiteDistribution_prob_le_one` | one lemma `FiniteDistribution.prob_le_one` next to the structure (`MDP/CoreDefinitions` or a new `MDP/FiniteDistributionLemmas.lean`) |
| `abs_apply_le_norm` | `TDInference/Noise.lean:61` and `Probability/StdGaussianPi.lean:190` (sup norm on `ι → ℝ`); `RLHF/VPO/Grid.lean:51` (`EuclideanSpace`) | sup norm: Mathlib `norm_le_pi_norm` with `Real.norm_eq_abs`; Euclidean: look up the `PiLp`/`EuclideanSpace` coordinate bound before adding one |
| `mulVec_smul_eq_smul_mulVec` | `Probability/LindebergFinite.lean:65` | Mathlib `Matrix.mulVec_smul` / `Matrix.smul_mulVec` (`smul_mulVec_assoc` is deprecated at the pinned Mathlib) |
| `sum_fin_succ_snoc` | `TDInference/PathMarginals.lean:26` (`StatisticalRL.Fintype`), `Probability/LindebergFinite.lean:351` (`sum_fin_succ_snoc'`) | one generic copy in `Probability/` or `Analysis/` |
| `expectation_mono`, `expectation_le_const` | `MDP/Basic.lean:49,57`; `MultiAgent/ModelBased/BestResponse.lean:57`, `MultiAgent/LowerBound/Values.lean:45` | `MDP/Basic` |
| `pathWeight_nonneg`, `sum_pathWeight` | `MDP/FiniteTrajectory.lean:58,69`; `TDInference/Definitions.lean:170,175` | `MDP/FiniteTrajectory` (the two `pathWeight`s may be different functions; check before merging) |
| `FiniteDistribution.ext_prob` | `MultiAgent/Hedge/Stage.lean:26`, `OfflineRL/FiniteVILCB/RowEvents.lean:29` | next to `FiniteDistribution` |
| `finiteDistribution_ext` | `MultiAgent/ModelBased/Event.lean:80`, `OfflineRL/BernsteinInfiniteData.lean:88` | same |
| `pointMass_prob_self` | `MultiAgent/ModelBased/CE2Game.lean:29`, `OfflineRL/FiniteVILCB/Links.lean:54` | `MDP/PointMassDefinitions` |
| `log_two_gt` | `Federated/Sync/Rate.lean:25`, `ModelFree/FiniteQ/Arithmetic.lean:17` | Mathlib `Real.log_two_gt_d9` |
| `cnt_zero`, `cnt_succ`, `cnt_mono`, `cnt_le` | `ModelFree/AsyncQ/Weights.lean:21,23,30`, `ModelFree/AsyncQ/Path.lean:21`; `OfflineRL/FiniteLCBQ/Counting.lean:24,26,39,43` | separate `cnt` definitions; merge only if the definitions agree |
| `weight_nonneg`, `sum_weight_sq_le` | `ModelFree/AsyncQ/Weights.lean:77,82`, `ModelFree/FiniteQ/Weights.lean:97,140`; `weight_nonneg` also `Generative/FiniteHorizonLowerBoundBounds.lean:86` | separate weight definitions; check before merging |
| `list_sum_map_eq_finset_sum_of_nodup` | `RobustRL/TVSortedStateMass.lean:107`, `RobustRL/TVSortedThreshold.lean:11` | Mathlib `List.sum_toFinset` (additive form of `List.prod_toFinset`) |

The paths above are the post-move (2026-11-10) module paths; the line numbers date from 2026-11-08 and may have
drifted. Old paths resolve through `layout-moves.json`.

## 5. Moving modules

Tool: `scripts/move_modules.py` (tests: `scripts/tests/test_move_modules.py`).

```sh
python3 scripts/move_modules.py --map docs/layout-moves.json --dry-run      # prints every change, writes nothing
python3 scripts/move_modules.py --map docs/layout-moves.json --apply --all-docs --lean-comments --delete-stale
```

`--all-docs` also rewrites links, module names and path tails (`Ch7Rest/Marl76Defs.lean`, unique bare file names) in every text
file under `docs/`, `site/`, `scripts/`, `.github/`, `ci/` and the top-level `*.md`, except hash-pinned records
(`docs/validation/`), generated files (`docs/graph/`, `docs/NEXT.md`), the map, this file and the tool; `--keep-history`
additionally leaves `docs/critic-*` and `docs/builder-*` untouched. `--lean-comments` rewrites the same mentions inside Lean
comments and docstrings only. A map entry may carry `"allow_statements_source": true` to move a non-index module out of
`Statements/`; the index files themselves (`ChN`, `ChNProofs`, `QLearningProofs`) are always refused. The 2026-11-10 move
used `--all-docs --lean-comments`, so review records now cite post-move paths (prose that names old file stems
was left as is).

- It rewrites only header `import` lines in `Formalization/**/*.lean`, `Formalization.lean` and `Audit.lean`;
  `Formalization/<path>.lean` links and `Formalization.<module>` names in `docs/COVERAGE.md`,
  `docs/named-result-status.json`, `docs/SOURCE-ISSUES.md` and `README.md`; and the keys in
  `scripts/gates/*.txt`. Without `--all-docs`, historical review records (`docs/critic-*`, `docs/builder-*`, …) are not edited: they are
  evidence pinned to past commits. Use `layout-moves.json` to resolve old paths in them.
  Markdown link text equal to the old file name (or its path tail) is renamed with the link, for example
  `[Marl76Defs.lean](…/Ch7Rest/Marl76Defs.lean)` → `[Definitions.lean](…/MultiAgent/ModelBased/Definitions.lean)`.
  Bytes outside rewritten names, line endings included, are preserved.
- It never edits a declaration, a namespace or any Lean byte outside module names in header `import` commands
  (an import after a block comment on the same line is handled; an `import` after the header is refused). It
  reports path mentions inside Lean comments and glob mentions (`Ch7Rest/Marl77*.lean`) in docs for manual
  follow-up.
- It refuses moves to or from `Statements/` (case-insensitively), existing targets, targets whose file or any
  directory component differs only in case from an existing path or another target (that works on macOS and
  breaks on Linux CI), duplicates and chains.
- `--apply` refuses when any touched path has uncommitted changes (override: `--allow-dirty`). On any failure it
  rolls the working tree back and says so; if the rollback itself fails it prints a `git restore` recovery
  command.
- `--delete-stale` unlinks the old modules' artifacts, only regular files inside this project's own `.lake/build`.
  It refuses when `.lake` or `.lake/build` is a symlink or resolves outside the project: dependency builds are
  linked read-only and must never be deleted through a link. Without the deletion, a forgotten import of an old
  module can still resolve against a stale `.olean` and a local check can pass falsely.
- The map is cumulative: applied entries are not moved again, but their references are still rewritten and
  checked, so rerunning the same map repairs a crashed run or an old-path import that a branch added later. After a
  move lands, set each entry's `status` to `applied` and fill in `pr` and `date`.

In the same change as the move, also:

- run `python3 scripts/gen_nodes.py` to regenerate `docs/graph/nodes.json` and `docs/NEXT.md` (their input hashes
  change; `gen_nodes.py --check` in `scripts/run_before_push.sh` fails otherwise);
- refresh this file: the §2 table, the §3.1 edge list and the §4 file:line column cite paths of the moved modules;
- fix the glob and prose mentions that the dry run lists under "manual follow-up".

A move needs a quiet window: no builder writing the affected directories, no full check running, and no open PR
touching `Formalization.lean`. Then run the full local check and the static gates. Namespace renames
(`StatisticalRL.Ch7Rest.*` → `.MultiAgent.*`), unifying the Statements namespaces, and renaming Statements files are
out of scope. Each would change cited declaration names and needs its own proposal with deprecated aliases and a
ledger migration.
