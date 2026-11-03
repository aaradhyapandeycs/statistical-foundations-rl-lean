# Independent source review: synchronous TD sampling interface

**Reviewed staged file:** `.local/TDSynchronousSampling.lean`, SHA-256
`eefb37396308721f28a33ef29b90001f3934f954d7b2c330e36cda22b60fe182`.
The handoff is `docs/builder-td-synchronous-sampling.md`. The initial
semantic review was source-only. A later independent exact-source compile and
axiom audit is recorded below.

**Authoritative source:** `source/upstream/tex/chapters/generative_model_model_free.tex`,
SHA-256 `7f4eb058e00480bc0694cac93ac41e22f4cfe48aa58a00c4ccf909f805e60b22`.
Algorithm source lines 90–126 states the synchronous update and independent
per-state sample from `Pπ(·|s)` at each iteration; Algorithm `alg:td-infinite`
at lines 150–169 makes the `t=1,…,T` indexing explicit. The policy-induced
transition definition is `Formalization/MDP/Basic.lean`, SHA-256
`ecf28ee04a78405be352f5453d957f34a7883d33304b21255a9f7f444e0bc088`, where
`policyTransition` is the actual policy-action mixture followed by the MDP
transition.

## Findings

- `tdSamplingLaw` delegates to the actual finite product experiment indexed
  by `State × Fin (T+1)`. Each coordinate has the `M.policyTransition π s`
  row law by the reused marginal theorem, and the reused `iIndepFun` theorem
  makes all state/time coordinates mutually independent. This is consistent
  with fresh synchronous generative draws, and is stronger/more explicit
  than only asserting per-time marginals. The sample carrier is finite from
  the declared `Fintype State` and `Fin (T+1)`.
- The update in `tdIterate` at step `t+1` uses exactly
  `η (t+1)`, `policyReward M π s`, and the previous iterate at
  `samples (t+1) s`. These are the source's equation `eqn:td-learning-0` /
  `eqn:td-learning`, with synchronous use of `V_t` at the sampled next
  state. `policyTransition` matches the source's `Pπ` row, including the
  action mixture for a randomized stationary policy.
- The finite array is indexed by `Fin (T+1)`, and `tdSamplesExtend` maps
  natural time `t<T+1` to that coordinate. For the iterate at `T`, recursion
  consumes only coordinates `1,…,T`; coordinate `0` is unused. For `T=0`,
  the iterate is `V₀` and the sole coordinate is unused. Out-of-range
  extension by a fixed nonempty state is harmless for these finite iterates.
- The actual link is definitional: `tdSampledIterate` is `tdIterate` applied
  to that finite-array extension. Its measurability follows on the finite
  data space; `tdSampledIterate_bounds_ae` is proved pointwise from the
  deterministic `tdIterate_bounds`, so the probability law is not used to
  hide any exceptional outcomes. The step-size bounds are explicit through
  `T`, and initialization uses the actual effective-horizon interval.

## Caveat and scope

The source algorithm samples only times `1,…,T`; the staged interface uses an
enlarged `(T+1)`-coordinate product with an unused independent time-zero
coordinate. This does not change the distribution of the iterate, since the
definition ignores that coordinate, but the file does not export an explicit
projection/marginal theorem identifying its output law with the exact
`T`-draw algorithm sample space. If a later theorem states the source law
directly, prove that finite-coordinate projection once rather than describing
the augmented carrier as literally the source's raw sample array.

The handoff accurately limits its claims: there is no exported natural
filtration/causality theorem, iterate-versus-past independence claim,
martingale-difference identity, concentration theorem, convergence rate, or
infinite-time path law. No gap in the product marginals, synchronous update
semantics, finite measurability, or pathwise iterate bound was found in this
interface.

## Independent staged compile and axiom audit

Verified the exact source hash, then compiled it with
`bash scripts/lean-local.sh -o .local/td-synchronous-sampling-independent-audit/TDSynchronousSampling.olean .local/TDSynchronousSampling.lean`; exit 0 with no diagnostics. A separate
import audit compiled successfully against that fresh output. Probed
`TDSamples`, `tdSamplingLaw`, its probability instance, both sampling-law
theorems, `tdSamplesExtend`, `tdSampledIterate`, its measurability theorem, and
the almost-sure bound theorem. `TDSamples` is axiom-free; every other probed
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
The audit source/output are in
`.local/td-synchronous-sampling-independent-audit/`.

**Verdict:** semantic pass with the harmless extra-coordinate qualification
above. The staged source now has independent compile and axiom evidence; the
source-law projection caveat and production integration remain outstanding.

Production integration: the relevant production module bodies match the independently reviewed staged sources, with qualified imports where needed. The complete project build compiled the actual exports and audited 2,279 declarations, permitting only `propext`, `Classical.choice`, and `Quot.sound`.
