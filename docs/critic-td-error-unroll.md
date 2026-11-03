# Independent review: finite TD error unrolling

Reviewed `.local/TDErrorUnroll.lean`, SHA-256 `495d294dae15f39fd1fe7a4f07fc7a202eec9dddf0686a15fd36f56555538e48`, against `TDErrorDecomposition.lean` SHA `c0a838360290c7d47e16a0228d5a4ecfbfee06ddfc354a9e2ba4df07241a51fe` and source equations `eq:Delta-t-recursive-decomp-TD`, `eq:defn-xit-TD`, and `eq:TD-Zk-defn` in `source/upstream/tex/chapters/generative_model_model_free.tex:341–366`.

## Source/semantic review

PASS for the exact terminal-time error telescope. The initial term is the actual `V₀−M.trajectoryExpectedValue π`. At step `t+1`, induction applies the one-step linear transition to the initial term and every existing terminal-t increment, then adds the new diagonal increment. The `Finset.Icc 1 t` range therefore becomes exactly `Finset.Icc 1 (t+1)`; at t=0 it is empty, so the base case gives the initial error without a sample or noise term.

The propagator's recursion applies update operators in chronological order: `tdErrorPropagate k t` leaves its input unchanged at `t=k` and applies the operators at source times `k+1,…,t`. Thus an innovation from update k is propagated only by future factors, as in the source product. The scalar factor `γ η_k` is carried outside by linearity. For the newly added diagonal k=t+1, the propagator is the identity and the term is exactly the positive centered-row fluctuation at that update. No commutativity assumption or reversed operator order is used.

Indexing agrees with the TD update: Lean update `k+1` uses old iterate `V_k` and sample `samples(k+1)`. `tdCenteredRowNoise` at `k+1` is `V_k(sample)−PπV_k`; multiplying by `γ η_{k+1}` gives the source innovation. Rates and samples are unconstrained functions in this theorem. The proof is pathwise algebra; it assumes no sampling law, independence, conditional centering, integrability, or concentration premise.

## Fresh exact-source compile and axiom audit

The hash-pinned script `.local/audit-td-error-unroll-independent.sh` rebuilt the exact staged decomposition and unrolling sources in order under `.local/td-error-unroll-independent-audit`, and rechecked the imported production dependency hashes. Both modules compiled without diagnostics. An import probe covered 17 declarations from the two staged modules; every export used only `propext`, `Classical.choice`, and `Quot.sound`.

## Limits

This closes the finite pathwise identity only. It does not establish the TD innovations' conditional mean or variance, a martingale difference sequence, a conditional variance bound, Freedman applicability, or any stochastic accuracy/rate theorem. The propagator representation is kept as a function recursion; a later matrix-product identification would require its own proof.

Production integration: reviewed source declarations and proofs compile under production module names; staged imports and stale staging-only comments were updated. The complete project export compiled and audited 2,863 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
