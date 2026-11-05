# Independent source review: fixed-terminal Q-learning optimal-value fluctuation

The source review was followed by an independent exact-source compilation. Exact current staged hashes match the builder handoff:

- `QLearningOptimalFluctuationDraft.lean` (private staged draft, not shipped): `2bfbc447af7d3ca3616cd1c6abce92acf3d2fdacbf85655bcaa73923f2b14655`.
- `QLearningOptimalFluctuationMomentsDraft.lean` (private staged draft, not shipped): `c2fc20dace8514ce247f8928e8bcc3a138736b8bc77ce6a77d8a882a04707d97`.

## Source and indexing

The value used is the actual trajectory state value of `M.optimalGreedyPolicy`, which the production optimal-trajectory module proves attains the optimality fixed point and dominates every stationary policy. It is fixed by M before any training array is sampled. The centered draw at zero-based layer t is `V*(Y_{t,s,a})−P_{s,a}V*`; this layer is source update i=t+1.

For a fixed source terminal u, the active summand is

`γ η_i ∏_{j=i+1}^u(1−η_j) · (P_i−P)V*`,

where `i=t+1` and `⌊T/2⌋<i≤u`. The staged `qPositiveWeight` has the correct positive-index source product: for i=u its suffix product is empty and the weight equals η_u. The window test `T/2 < t+1` uses natural-number division and matches the source floor. The sum definition iterates over the actual T layers and zeroes inactive layers; its identification with the entire source sum still requires the stated `u≤T` premise and a proved index-reindexing theorem.

## Moment findings and scope

The indicator-pullout proof uses the actual q-sampling row marginal and full strict sample-prefix sigma algebra. For each active layer, it proves conditional mean zero and the exact conditional square `γ²(η_i^(u))² Var_{P(·|s,a)}(V*)`. Inactive layers—including t≥T—are identically zero. These equalities do not require the weights to be nonnegative; the separate weight lemma correctly assumes `0≤η_i≤1` on actual indices only to prove weight nonnegativity. `qTrueOptimalValue_bounds` supplies `0≤V*≤1/(1−γ)`, so a subsequent coarse moment cap can use the true row variance bound and the deterministic schedule weights.

The handoff correctly leaves open the source-sum identity, adaptation/natural-history transfer for this distinct weighted sequence, its deterministic increment and summed variance caps, and Freedman application. The existing Q natural-history theorem is for the iterate-dependent `qRowIncrement` using `V_t`; it does not directly prove adaptation or moment transfer for this `V*` weighted process. A sample-prefix filtration with fixed-terminal zero-padded increments is the direct source-compatible route.

This `V*` fluctuation corresponds to the monograph's loose error decomposition, which it controls by Azuma. It is not the distinct `V⁺`/`V⁻` deterministic-comparison fluctuation in the sharp Freedman proof; this module is not a proof of that sharp comparator event or the final Q-learning rate. No source-level mismatch found in the reviewed definitions or conditional moments.

## Independent compilation and axiom evidence

Rebuilt `QLearningOptimalFluctuationDraft.lean` (private staged draft, not shipped) and `QLearningOptimalFluctuationMomentsDraft.lean` (private staged draft, not shipped) into an isolated local audit directory (not shipped), using the previously audited exact Q-learning conditional-pullout closure. The target and dependency hashes were checked; both target builds succeeded. All 11 target definitions/theorems were import-probed and use only `propext`, `Classical.choice`, and `Quot.sound`. This remains staged compiler evidence, not production-module integration/export validation.

Production integration: the reviewed source declarations and proofs compile in the project export with qualified production imports and updated staging-only comments where applicable. The full project audit checked 2,970 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
