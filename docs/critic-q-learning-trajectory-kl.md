# Independent audit: one-step trajectory KL chain rule

Reviewed exact staged source `.local/QLearningTrajectoryKLDraft.lean`, SHA-256 `a15d69448bdb00eb75e31ee9d09e92278b7fb8a4e98ca40c05567ef2e83cfba2`. The source review, isolated compile and export axiom probes are complete. This is a generic one-step Markov-law identity; it is not the finite-horizon policy trajectory chain rule or the geometric stopping-time result.

## Source semantics, normalization, and KL orientation

The actual joint law is

```text
J(x,y)=μ(x)K(x,y),    J'(x,y)=μ'(x)K'(x,y).
```

Its `sum_prob` proof expands the product carrier sum, sums each normalized transition row first, then uses `sum μ=1`. It represents the joint law of current and next state under the stated actual finite distributions; it does not assume a product of two independent states.

The exported identity is oriented `finiteKLExpression(J',J) = finiteKLExpression(μ',μ) + E_{x∼μ'} finiteKLExpression(K'(x),K(x))`. The repository expression is `Σ u(x) log(u(x)/v(x))`, so the atomic expression has the exact `KL(primed || baseline)` orientation throughout. To call each side actual measure-theoretic KL, a consumer must additionally use the finite `klDiv`/expression bridge under the support-derived absolute continuity. It agrees with the source trajectory equation `eq:KL-ub-k-rho-proof` in `generative_model_model_free.tex`, lines 2660–2667, which uses `KL(P'_k || P_k)` and row terms `KL(P'(·|s,a) || P(·|s,a))`. It is not reversed.

Support assumptions are only the needed absolute-continuity inclusions: positive primed initial mass implies positive baseline initial mass, and for every x, positive primed transition mass implies positive baseline transition mass. The joint numerator is positive exactly when both primed factors are positive; the support hypotheses then prove both baseline factors positive, making the log factorization legal. When either primed factor is zero, the pointwise identity is established separately by the repository's totalized zero-term convention. Thus the proof does not divide by a zero baseline mass or require blanket strict positivity. The row support premise is stronger than necessary for rows with μ'(x)=0, but is precisely the reusable statewise kernel support condition used for Markov iteration and is compatible with the source uncertainty-set support restriction.

The conditional term is averaged under μ', as required: after the pointwise split, summation over y uses `Σ_y K'(x,y)=1` to recover the initial KL term and leaves `μ'(x)` multiplying each row KL. No target conclusion is assumed in the proof.

The draft establishes one step only. To obtain the source's conditional-on-τ=k trajectory law, a separate induction must handle the fixed common initial `(s₀,a₀)`, each next-state transition, shared policy action draw, path carrier, and k=0 unit-law case. The current theorem does not prove that identification, nor the random stopped-prefix mixture, Pinsker, or value comparison.

## Fresh isolated compile and transitive axioms

Exact source `.local/QLearningTrajectoryKLDraft.lean` compiled with exit 0 and no diagnostics to `.local/q-trajectory-kl-source-independent/QLearningTrajectoryKLDraft.olean` using the repository's pinned Lean runner:

```text
bash scripts/lean-local.sh -o "$PWD/.local/q-trajectory-kl-source-independent/QLearningTrajectoryKLDraft.olean" .local/QLearningTrajectoryKLDraft.lean
```

Fresh `ImportAudit.lean` probes `qMarkovStepLaw` and `qMarkovStep_finiteKL_chainRule`. Both transitive axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; see `.local/q-trajectory-kl-source-independent/axioms.log`.

The draft imports production `Formalization.MDP.Basic` and production `Formalization.Generative.GenerativeLowerBoundFiniteKLDataProcessing` (SHA `471ec68b7d653a1bdace8e73097dbd5f85c5d7f9c5e6f4d714759a52b1c88aa9`). Its related production source hashes at audit time are `GenerativeLowerBoundFiniteDataProcessing.lean` `9022df9d0638c5d1624c4f83934a1b72739021f5a49d82eddb19817ba05904e7` and `GenerativeLowerBoundKLAffinity.lean` `15a65644d6489fec79dc127efe58ba00cb33ff03b0a3dfc9483e5c9daf35bded`. Compilation consumed existing project dependency artifacts and did not rebuild shared packages.

No source/semantic mismatch was found for the one-step theorem. This does not establish a trajectory theorem or production integration. The compiler slot was released after the audit.

## Production integration

The reviewed finite one-step Markov KL chain rule is integrated as `Formalization/ModelFree/QLearningTrajectoryKL.lean`; full forced-prefix and geometric-stopping stability remain separate. The declaration and proof bodies match the reviewed staged source; imports and status comments were updated where required. The full project check compiled 258 modules and audited 3,407 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
