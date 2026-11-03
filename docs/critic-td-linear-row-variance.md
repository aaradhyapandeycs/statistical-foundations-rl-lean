# Source review: TD linear-row conditional variance foundation

Source-only review; no compiler was run. Reviewed `.local/TDLinearRowVariance.lean`, SHA-256 `b0068f5663d1edb5e298693aebaae7abb63facbfa2963e6c1f8cd0074c7f14c9`, with the previously reviewed `TDCrossCovariance` and `TDConditionalMoments` sources. The mathematical target is the source bound `eq:Var-u-Pk-v-bound` and its application `eq:TD-var-Zk-upper-bound-each-term` in `generative_model_model_free.tex:506–530`.

## Findings

- The conditional law is the actual finite TD sampling law, conditioned on `tdPastSigma T k`. That prefix contains used source times 1 through k; the fresh coordinates are at source time k+1. The old iterate `V_k` and its row means are therefore prefix-predictable. The target source `TDConditionalMoments` and `TDCrossCovariance` lemmas provide the correct diagonal and off-diagonal moments for this same iterate and layer.
- `tdRowIncrement_condExp_pair` combines the diagonal squared-moment theorem and the distinct-state conditional cross theorem. The result is `Var_{Pπ(s)}(V_k)` on the diagonal and zero off the diagonal.
- For arbitrary deterministic real coefficients u, `tdLinearRowIncrement_condExp_sq` expands the square into a finite double sum and uses those pair moments. It correctly retains squared row coefficients `u(s)^2`; no nonnegative-weight assumption is smuggled into the equality.
- The later proxy inequality separately assumes `u(s)≥0` and uses nonnegativity of true-row variance `v(s)≥0`. It proves `Σ_s u(s)^2 v(s) ≤ (Σ_s u(s))(Σ_s u(s)v(s))`, matching the max-row-mass inequality in the source. This is the right scalar form of the source's row-mass variance proxy.

## Exact scope and gap

The module is generic in u and does not identify u with a row of the actual fixed-terminal propagator. That is an appropriate boundary: source consumption still requires proving the chronological propagator's coefficient representation, nonnegative entries, exact row mass/suffix product, and matching the source indexing `i=k+1`. In particular, for source (Z_{k+1}^{(\tau)}), the coefficient row should be γη_(k+1) times the propagator from updates k+2 through τ; then its total mass is the source scalar weight. Only after that identification can the generic proxy yield equation `eq:TD-var-Zk-upper-bound-each-term`.

No learning-rate, initial-value, bounded-iterate, or source late-terminal assumptions are needed for this finite conditional identity. The nonnegative coefficient premise is needed only for the proxy inequality. No terminal-independent process, deterministic variance cap, or Freedman application is proved here. No source-level issue found in the prefix, cross-term cancellation, coefficient powers, or proxy inequality.

The requested builder handoff was not found under `docs/` during this review; this note therefore records mathematical/source findings without asserting compilation or axiom evidence.

## Independent exact-source compilation and axioms

The exact module and staged dependencies were subsequently rebuilt into `.local/td-linear-row-variance-independent-audit`: `TDCausality` SHA `8c8cfdf1271c2bd9736b9ec0eb8b3da7896f8f3f9c4bfd03ca33af1a6249fb29`, `TDErrorDecomposition` SHA `c0a838360290c7d47e16a0228d5a4ecfbfee06ddfc354a9e2ba4df07241a51fe`, `TDConditionalMoments` SHA `1edb87f6d84c82a9e1d242aae2dbac95701d33b173eda2f08d65deb4a9d6c227`, `TDCrossCovariance` SHA `709c414fef2264b3ef7b3790873ba0d3d813f87973cb447a01880c7ca86b1744`, and `TDLinearRowVariance` SHA `b0068f5663d1edb5e298693aebaae7abb63facbfa2963e6c1f8cd0074c7f14c9`. All compiled successfully. The five target declarations were import-probed and each uses only `propext`, `Classical.choice`, and `Quot.sound`. This is fresh staged closure evidence; production export checking remains separate.

Production integration: the reviewed source declarations and proofs compile in the project export with qualified imports and updated staging-only comments where applicable. The full project audit checked 3,029 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
