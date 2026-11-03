# Independent audit: fixed-`V*` Q-learning row/time Freedman union

Reviewed exact staged source `.local/QLearningOptimalFreedmanUnionReviewDraft.lean`, SHA-256 `a38749f251d4411118d15a5eee13e4ab2f09aa58b0ecf26388fa0f0c9ac7c407`. Source review and a fresh isolated compile/axiom probe are complete. This proves only the staged union result and its actual imported fixed-row result; it is not the source's printed Azuma theorem or the final Q-learning error theorem.

## Source and semantics

The actual loose Q-learning analysis is in `source/upstream/tex/chapters/generative_model_model_free.tex`, SHA `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`. The fixed-​optimal-value fluctuation is described around lines 1244–1263: for each fixed terminal `t`, `xi_t = gamma Σ_{i=floor(T/2)+1}^t eta_i^(t) (P_i−P)V*`, where `V*` is the actual deterministic optimal trajectory value. The source uses Azuma and a row/time union to obtain its printed radius with `log(4SAT/delta)` and confidence at least `1−delta`.

The reviewed draft unions the already established actual-law self-normalized Freedman event for that same fixed deterministic `V*` fluctuation. It does not replace `V*` by a fitted or data-selected continuation. The fixed terminal sequence uses the full finite product experiment of length `T`; source update `i` uses the actual layer `i` (sample coordinate `i−1` in the staged zero-indexed sequence). Its event quantifies over every `State`, every `Action`, and `j : Fin T` with `T/2 < j.val+1`, so the covered positive source terminals are exactly the late terminals `floor(T/2)<u≤T`, including `u=T` and excluding the boundary `u=floor(T/2)`.

For each tuple in `State × Action × Fin T`, the bad-event allowance is `epsilon=delta/(S*A*T)`. Non-late terminal tuples get the empty bad event. There are exactly `S*A*T` tuples; the finite union bound gives total failure at most `delta`, without assuming any independence among overlapping events. The MDP supplies nonempty finite state/action carriers, and `T≥2`, `0<delta<1` imply `0<epsilon<1`. The fixed-row Freedman result additionally retains `c1,c2>0`, the exact source rate schedule, `u≤T`, `K>0`, and its explicit confidence-domain assumptions. The row event preserves the exact `log(2K/epsilon)` threshold and predictable-variance term; no unsupported simplification of its radius is made.

The reviewed source is a repaired copy of `.local/QLearningOptimalFreedmanUnionDraft.lean` (earlier SHA `742d3329e0c5c3929a3f0ee4615646d9ff8db5e95f3422115c59edb0459a18ee`). The only proof changes normalize the finite product cardinality from `S*(A*T)` to the source denominator `(S*A)*T` with `ring`, and provide the established nonzero denominator to `field_simp`. The exact final theorem assumptions, event, confidence allocation, and underlying fixed-row radius are preserved.

## Fresh isolated compile and axiom evidence

The exact final source compiled with exit 0 and no diagnostics to `.local/q-optimal-union-independent-audit/QLearningOptimalFreedmanUnionReviewDraft.olean` using:

```text
bash scripts/lean-local.sh -o "$PWD/.local/q-optimal-union-independent-audit/QLearningOptimalFreedmanUnionReviewDraft.olean" .local/QLearningOptimalFreedmanUnionReviewDraft.lean
```

A fresh import-only audit at `.local/q-optimal-union-independent-audit/ImportAudit.lean` probes the good-event definition and union theorem. Both transitive `#print axioms` outputs contain only `propext`, `Classical.choice`, and `Quot.sound`; see `.local/q-optimal-union-independent-audit/axioms.log`.

The reviewed wrapper's production import is `Formalization.ModelFree.QLearningOptimalFreedman`, exact source SHA `c96904f5c9d16f7081a1aa6a9aabb4f87c5674244617bbefeb65f972980c6b7c`; it imports `QLearningOptimalPredictableVariance`, SHA `c7841d56a63715ff3ed18de06664acb0916168cfbbaae305f45f5d32f6eb5bda`. This compile consumed their existing project artifacts and did not rebuild dependencies. The exact wrapper source remains hash-pinned above.

## Boundary

This is an alternative Freedman-based common event for the source's fixed-`V*` fluctuation. It neither proves equality with nor domination by the source's displayed Azuma radius. It does not prove robust `V+`/`V−` fluctuation events, absorb fluctuations into robust residuals, or establish the final Q-learning rate. The theorem is staged and has not been integrated as a production declaration.

## Production integration

The reviewed fixed-V* simultaneous event is now integrated as `Formalization/ModelFree/QLearningOptimalFreedmanUnion.lean`; robust-comparator events and the final rate remain separate. The declaration and proof bodies match the reviewed staged source; imports or status comments were updated where required. The project-wide check compiled 250 modules and audited 3,333 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
