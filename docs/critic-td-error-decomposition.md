# Independent review: one-step TD error decomposition

Reviewed `.local/TDErrorDecomposition.lean`, SHA-256 `c0a838360290c7d47e16a0228d5a4ecfbfee06ddfc354a9e2ba4df07241a51fe`, against the synchronous policy-TD update and equations `eq:Delta-t-recursive-decomp-TD`, `eq:defn-xit-TD`, and `eq:TD-Zk-defn` in `source/upstream/tex/chapters/generative_model_model_free.tex:278–366`.

## Source/semantic review

PASS for the pathwise one-step identity. `tdErrorValue` subtracts `M.trajectoryExpectedValue π`, the actual infinite-horizon return under the stationary policy. The proof obtains its Bellman equation from `M.valueFixedPoint_spec` and the proved bridge from the actual trajectory expectation to the value fixed point; there is no target-shaped fixed-point hypothesis.

The update and noise indices align: the successor at `k+1` uses the old iterate `V_k` and the draw `samples (k+1)`. The centered row noise is `V_k(samples (k+1,s))−E_{Pπ(·|s)}V_k`; after multiplication by the positive factor `γ η_{k+1}`, this is exactly the source's `η_k γ(P_k−Pπ)V_{k−1}` under the shift from source time k to Lean time k+1. The sign is correct. The deterministic transition is `(1−η_i)U+η_iγPπU`, i.e. `I−η_i(I−γPπ)`. No bounds on η, sampling distribution, independence, or conditional-expectation premise is assumed for this algebraic identity.

The propagation recursion starts applying the source operator at `start+1`, proceeds chronologically through `finish`, and applies no operator when `start=finish`; this matches the future-factor product in the fixed-terminal increment definition. The terminal-time parameter t is explicit in `tdWeightedErrorIncrement`; future rates are deterministic parameters. The zero convention outside `1≤k≤t` and for the unused time-zero noise is compatible with the finite sum over source updates.

## Exact-source compile and axiom audit

Verified the staged source hash and compiled it without diagnostics using:

```sh
bash scripts/lean-local.sh -o .local/td-error-decomp-independent-audit/TDErrorDecomposition.olean .local/TDErrorDecomposition.lean
```

An isolated import probe checked all eight public declarations: the five definitions, the two linearity lemmas, and `tdErrorValue_succ`. Every export uses only `propext`, `Classical.choice`, and `Quot.sound`. Imported production sources at audit time were `TDSynchronousSampling` SHA `eefb37396308721f28a33ef29b90001f3934f954d7b2c330e36cda22b60fe182`, `PrefixValueBridge` SHA `bd286567aa059c3e5fb293f1943eb06bd2e3d79c8dc9484d8a73195a2db16e89`, `TDLearningWeights` SHA `45cebbdcb5ff62d586b28932803ae727ec2f1d31bb814346c7e5886e3c19a59f`, and its transitive TD iterate module.

## Scope

This module proves the one-step pathwise identity and defines source-compatible weighted increments; it does not prove the full unrolled finite-sum identity yet. It also proves no conditional centering, conditional variance, martingale property, concentration bound, or TD rate theorem. Those remain separate obligations and cannot be inferred from this deterministic algebraic module.

Production integration: reviewed source declarations and proofs compile under production module names; staged imports and stale staging-only comments were updated. The complete project export compiled and audited 2,863 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
