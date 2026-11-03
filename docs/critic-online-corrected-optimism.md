# Source review: corrected UCBVI optimism implementation

## Status

The integrated [source allocation export](../Formalization/Online/SourceOptimism/SourceOptimismAllocation.lean) and its dependency chain state a strict factor-two optimism result for a fully specified corrected implementation. The source theorem’s event, confidence allocation, active stages, episodes, states, actions, and actual sequential law are represented. The explicit zero-visit convention remains a proposed correction to an undefined branch of the printed algorithm, so this result should not yet be described as the exact named source lemma `lemma:opt` without an approved source convention or erratum.

The production export matches the previously isolated canonical source reviewed at SHA-256 `34be0110a9cdf6e48450ff4bc381d891267ca06e11d252cb1e3bc84db8b3daf3`. The earlier isolated build compiled all 41 modules and ran a 174-export probe plus a six-export sigma probe. In that isolated run, `onlineSourceAllocated_allStageTrajectoryOptimism_strict` has transitive axioms only `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or project-specific axiom. The isolated run used a pinned snapshot of 339 project artifacts, whose hashes alone do not establish source-to-artifact provenance. The integrated working-tree and separate clean-copy builds subsequently passed on identical source hashes, and each audited 4,541 declarations for transitive axioms.

## The event and probability bound

For every episode, active stage, state, and state-action pair, the event compares the computed table against the actual trajectory return of the true optimal greedy suffix. The value comparison uses the trajectory value from the current stage onward. The Q comparison fixes the initial action and then follows the trajectory policy, including actions not chosen by that greedy policy. This matches the source’s optimal (V_h^*) and (Q_h^*) on finite-horizon suffixes.

Episode and stage indices are zero-based in Lean: episode `k` uses exactly the history from the preceding `k` completed episodes, and stage `h` corresponds to source stage `h+1`. The theorem covers all `k ∈ Fin K`, `h ∈ Fin H`, states, and state-action pairs simultaneously.

The law is the actual online sequential law. Episode resets are independent with initial distribution `ρ`; transitions are drawn from the selected state-action-stage row; and each action uses the same fixed greedy planner built from the completed history. The empirical row contains exactly the previously observed outcomes for that row. No iid claim conditional on a random visit count is used.

The allocation is exactly

\[
\delta' = \frac{\delta}{100 S^2 A^2 H^2 K^2},
\]

using the printed denominator 100. The row index set has size `SAH`, with no extra terminal stage. Consequently the bound is strictly

\[
\Pr(\text{all active }Q,V\text{ comparisons hold}) > 1 - 2SAHK\delta'.
\]

## Proof route

The concentration event is formed for each fixed row and each deterministic sample-prefix length, using the true optimal suffix continuation. A single simultaneous event covers whichever prefix length the adaptive algorithm realizes. This avoids conditioning an iid concentration theorem on the random visit count. The event is transferred to the actual online trajectory law through the finite reset/path atom comparison and stack/sequential law equality; the observed-history event is obtained by inclusion, without asserting that a counterfactual all-prefix event is history-measurable.

On that event, the source-compatible Bernstein certificate is consumed by the deterministic capped backup. Backward induction gives Q optimism, and the greedy value table gives V optimism. The planner chooses one fixed deterministic maximizing tie rule from the same capped Q table. The route establishes the candidate’s factor-two probability bound; it does not alter the manuscript proof, whose final union-bound paragraph gives factor four despite the printed factor-two lemma.

The finite sigma support is handled by a separate helper: the default finite Pi/product measurable structure on the reset/path atom carrier is shown to be top, and the measure/map wrapper transports across that equality. This is scoped to the finite atom carrier used by the law comparison; it is not a general measurable-space claim or an additional sampling assumption.

## Source caveats

1. **Unvisited rows.** Algorithm UCBVI initializes Q to H and empirical transition rows to uniform, then sweeps over every row and evaluates bonus terms containing division by `N_h(s,a)`. It does not specify what to do when that count remains zero. The implementation therefore makes the proposed choice `N=0 → Q=H`, retaining the uniform empirical row and leaving the positive-count formula unchanged. The source proof’s deterministic `N≤2` case uses Q=H, but that does not define the all-row zero-denominator update. Until the missing convention is approved, the result is a corrected implementation rather than the literal printed algorithm. See the [zero-visit source review](critic-online-zero-count-convention.md).
2. **Tie-breaking.** The result uses one fixed deterministic maximizer. It does not cover arbitrary or randomized tie-breaking, or a mutable implementation without a separate simulation argument.
3. **Factor discrepancy.** The manuscript’s lemma claims failure at most `2SAHKδ′`, while the final paragraph of its proof states `4SAHKδ′`. The fixed-prefix route above supports the candidate’s factor-two claim but does not resolve or silently repair that source inconsistency. See the [source-issues ledger](SOURCE-ISSUES.md).
4. **Build scope.** The prior isolated build and probes validate the candidate source set. The integrated working-tree and separate clean-copy builds and axiom audits passed on identical source hashes.

## Source references

- Algorithm UCBVI, `onlineRL.tex` lines 292–344 in [arXiv:2610.41903v1](https://arxiv.org/abs/2610.41903v1).
- Bonus and confidence allocation, lines 407–418.
- Named optimism lemma `lemma:opt`, lines 765–775.
- Its proof and the final factor-four statement, lines 3297–3395.
- [Capped backward recursion](../Formalization/Online/SourceOptimism/CappedBackwardRecursion.lean), [actual sequential law](../Formalization/Online/SourceOptimism/SequentialEpisodeLaw.lean), [observed-prefix probability](../Formalization/Online/SourceOptimism/ObservedPrefixProbability.lean), and [trajectory optimism](../Formalization/Online/SourceOptimism/GreedySequentialTrajectoryOptimism.lean).
