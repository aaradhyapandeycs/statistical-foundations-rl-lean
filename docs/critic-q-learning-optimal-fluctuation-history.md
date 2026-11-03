# Independent review: fixed-terminal Q-learning fluctuation history and caps

## Exact source and validation

Reviewed `.local/QLearningOptimalFluctuationHistoryDraft.lean`, SHA-256 `d05c9a25d561fc7d0df694e9eee00c979f1e3e964f8ab23e0672c63bb1693d6f`, matching the stable builder handoff. It depends on the previously reviewed fixed-terminal fluctuation/moment pair (`2bfbc447af7d3ca3616cd1c6abce92acf3d2fdacbf85655bcaa73923f2b14655`, `c2fc20dace8514ce247f8928e8bcc3a138736b8bc77ce6a77d8a882a04707d97`), iterate-dependent increment caps (`ca8a29d2bb7c1d60a8d52924da97df4d9011e5660eeb62be36d2df25edc154e1`), and natural-history bridge (`841361faa2ba6d092b6f46ccb15e0bcda03d591e147f74b1f6d611de334b7ffd`, `766309449c858a91456f82499c75e4de9c2af11fc8d6268f37f4e59815562c4f`). Those exact dependency artifacts were produced by the preceding independent staged audits.

Freshly compiled the exact target into `.local/q-optimal-fluctuation-history-independent-audit`. All seven public theorems were axiom-probed; each reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Source and semantic findings

- Source update i is stored at zero-based sample layer t=i−1. An active increment requires `t<T`, source window `T/2<t+1`, and `t+1≤u`; its coordinate is the actual row `(s,a)` at layer t under `qSamplingLaw M T`. The coefficient is deterministic and uses the exact positive-index source suffix weight `η_(t+1)∏_{j=t+2}^u(1−η_j)` multiplied by γ.
- The increment factors through `qPastData T (t+1)`: the only random coordinate is at layer t. Thus it is strongly measurable after that layer is observed. Every earlier increment j<t factors through prefix j+1≤t, proving the increment-generated strict history is contained in `qPastSigma T t`.
- Prefix conditional centering transfers to that smaller natural history by the tower property. This applies to active and inactive layers; inactive layers are zero by definition.
- On an active layer, the prefix conditional square is the deterministic squared coefficient times `qRowVariance` of the actual trajectory-optimal V*. Since V* and the coefficient are fixed before sampling, conditioning again on the smaller history preserves this constant exactly. The variance cap `qOptimal_rowVariance_le` is the actual transition-row variance bound from `0≤V*≤H`; the active magnitude cap uses rate assumptions `0≤η_k≤1` only for actual positive indices through fixed u.

The module does not export an explicit inactive-layer conditional-square/absolute-bound theorem, though each follows directly by simplifying the zero branch. It also does not supply a uniform cap independent of the source weights, a late-window sum-of-squares bound, the fixed-terminal sum/source reindexing theorem (which needs `u≤T`), the combined predictable variance cap, or Freedman/union-bound application. T=0 yields no active index; all increments are zero by definition. No source-level issue found in the exported statements.

This is staged evidence only; no production import or production-export check is implied. Keep the distinction from the iterate-dependent `V_t` increment and from the sharp proof's `V⁺`/`V⁻` comparison fluctuation.

Production integration: the reviewed source declarations and proofs compile in the project export with qualified imports and updated staging-only comments where applicable. The full project audit checked 3,029 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
