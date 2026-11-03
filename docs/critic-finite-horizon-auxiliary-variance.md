# Independent review: finite-horizon auxiliary variance sequence

## Source and scope

Reviewed staged source: `.local/FiniteHorizonAuxiliaryVariance.lean`, SHA-256 `19f843f138314e21a14d5b29eef88e758add4389dbbcfa7eb225e496bc68d4ee`.

The comparison source is Li et al., [*Breaking the Sample Size Barrier in Model-Based Reinforcement Learning with a Generative Model*, arXiv:2005.12900v8](https://arxiv.org/pdf/2005.12900v8), Section 7.2, PDF p. 20, equations (61)–(62), as mapped in `docs/source-finite-horizon-h3-proof-map.md`. The paper fixes a policy, initializes both sequences at the terminal stage to zero, uses ordinary policy value at level zero, and at each successor level adds the **true-transition** conditional standard deviation of the preceding level's next-stage true auxiliary value. The empirical recursion uses that same true-derived forcing and propagates only through the empirical transition.

## Semantic review

The source implements that recursion for deterministic nonstationary policies. `trueAuxiliaryValue` has the zero terminal suffix and level-zero reward-plus-true-transition recursion. At level `l+1`, it adds the square root of the true transition row variance of the next suffix's level-`l` value, then propagates the same level through the true row. `auxiliaryPolicyReward` exposes that forcing; `comparisonAuxiliaryValue` uses the true member of each stage pair to construct it and the second member's transition for propagation. This has the same shared-forcing orientation as (61)–(62), not an empirical variance reward.

The level-zero trajectory bridges are correct under the explicit shared-reward premise for paired models. The empirical specialization obtains that premise because `empiricalStages` changes transitions while preserving known rewards. The suffix congruence statements retain exactly the remaining stages and future policy actions. For each **fixed** policy and level, `empiricalAuxiliaryValueAt_factors_future` identifies the next-stage vector with a function of samples strictly after the current stage; `empiricalAuxiliaryValueAt_indep_row` then proves independence from the complete current `(state, action)` row under the actual `samplingLaw`. This matches the fixed-policy/future-sample semantics needed for a rowwise application.

## Limits and open obligations

- The independence theorem is for a policy `f` supplied as a fixed parameter. It does not establish that a data-selected fitted policy's suffix is independent of the current row. Such an application needs a separate causal backward-DP/tie-breaking factorization argument, as discussed in the source map.
- The module proves no auxiliary-level growth bound, level truncation, Bernstein residual event, probability bound, confidence allocation, or recursive unrolling. Its header correctly disclaims the growth estimate and conditional Lemma 9 premise. In particular, nonnegativity is established, but no uniform bound in the source's required class is proved; higher-level forcing is not constrained to the original reward range.
- The full trajectory bridge is stated at level zero and the episode start. Suffix dependence is separately formalized, but there is no general arbitrary-stage trajectory-value bridge here.
- Consequently this module formalizes the sequence and relevant fixed-policy independence prerequisite, not Li et al.'s Lemma 9 or the sharp `H^3` sample-complexity theorem.

## Independent compile and axiom evidence

After the source review, the exact staged file compiled into the fresh project-owned `.local/auxiliary-variance-independent/FiniteHorizonAuxiliaryVariance.olean` using `bash scripts/lean-local.sh -o .local/auxiliary-variance-independent/FiniteHorizonAuxiliaryVariance.olean .local/FiniteHorizonAuxiliaryVariance.lean`, with no diagnostics. An unchanged copy with `#print axioms` appended for all 24 top-level definitions/theorems also compiled via `bash scripts/lean-local.sh .local/auxiliary-variance-independent/FiniteHorizonAuxiliaryVarianceAxiomAudit.lean`. Every export reported only `propext`, `Classical.choice`, and `Quot.sound`. These checks use the currently available compiled imports; they do not rebuild dependencies or establish production integration. The temporary compile and axiom output remain under `.local/auxiliary-variance-independent/`.

Production integration: the reviewed source bodies compile in the project export, with qualified imports. In the seeded two-point risk module only, two local instance names were renamed to prevent collisions; the theorem statement and proof are unchanged. The full project check audited 2,373 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
