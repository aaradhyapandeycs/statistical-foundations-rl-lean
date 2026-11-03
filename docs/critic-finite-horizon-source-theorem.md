# Independent source review: finite-horizon sample theorem

Reviewed the exact staged files reported by the builder:

- `.local/FiniteHorizonSampleArithmetic.lean`, SHA-256 `d91617531b03261fcb62e7df6a3b80e0437d8311d9d85affa7ff28161ed753f5`.
- `.local/FiniteHorizonOneStage.lean`, SHA-256 `95866964fbc7fb725f8a22e21d8c9d2b9e4489027dbf552d019534dc7420850d`.
- `.local/FiniteHorizonMainSample.lean`, SHA-256 `d1301accb0d0759af368e5ea5a286dddf3d5388f47619e1d4aaef19725093562`.

Authoritative comparison: `source/upstream/tex/chapters/generative_model_model_based.tex`, SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`, especially algorithm and backward-planning discussion at lines 2526–2548 and `Thm:sample-compl-finite` at lines 2551–2575.

## Source quantifiers and algorithm

The existence theorem chooses `c₀=8640` before quantifying finite state/action carriers, `H`, the horizon-indexed environment `E`, natural per-row sample count `N`, a proof `hN:0<N`, fallback action, `δ`, and `ε`. It assumes `0<δ`, `0<ε≤H`, and the printed per-tuple budget `c₀ H³ log(HSA/δ)/ε²≤N`. Its conclusion is the actual sampling-law probability at least `1−δ` of simultaneous all-state/all-stage V and all-state/action/stage forced-first-action Q loss at most ε.

The implemented estimator is the deterministic causal `backwardGreedyActions` selector: each stage uses the local greedy action on the empirical stage, with the supplied fallback resolving ties. The source describes computing an optimal policy by backward planning but does not explicitly prescribe a tie rule. This is a concrete legitimate implementation of that algorithm; the theorem should not be read as uniform over arbitrary globally data-selected empirical-optimal tie rules. The common event and fitted continuation argument handle this causal selector, and the fixed true-optimal policy is handled on the same full sample array/law.

The formal conclusion is expressed as the interval `0≤V*−Vπ̂≤ε` and `0≤Q*−Qπ̂≤ε`, for every natural suffix start and all states/actions. Optimal-control domination supplies nonnegativity. Suffixes beyond the horizon are empty, so these extra natural-index cases are trivial strengthenings of the source's `h∈[H]` range. `E` carries the actual stage rewards and transitions; the empirical model retains the known rewards and estimates each `(h,s,a)` transition row from its actual N samples. The bound is per tuple, not total sample count.

## Positive sample convention and endpoint branches

All three staged declarations require `hN:0<N`; this is needed to define empirical frequencies. The source theorem calls N a sample size and uses an empirical frequency denominator N, so positive N is the natural algorithmic convention, but its displayed hypotheses do not separately write `N>0`. For `δ<1`, the displayed budget and nonempty carriers imply the needed positivity when its logarithm is positive. For `δ≥1`, the proof's probability conclusion is trivial from `1−δ≤0`, but positivity is not derived from the displayed budget. Thus the Lean theorem is explicitly for positive sample counts; removing that premise would require defining the zero-sample estimator or clarifying that positive integer N is implicit in the source's sample-size convention.

The proof first splits on `δ<1`. If `δ≥1`, probability nonnegativity suffices, with no logarithm-domain or concentration argument. When `δ<1`, it splits off `H=1`: known one-stage rewards and zero terminal continuation make true and empirical trajectory V equal for every policy, and forced-first-action Q is exactly the immediate reward. The event then has radius zero with probability one for all states/actions and every tie choice. For `H≥2`, the environment at stage zero supplies nonempty state/action types, so `T=HSA≥H≥2`; with `K=⌊log₂H⌋+1≤H≤T`, the explicit `β=2log(8KT/δ)` obeys `β≤10log(T/δ)`. Under `ε≤H` and the stated 8640 sample threshold, the arithmetic gives both strict `12Hβ<N` and radius `12H√(3βH/N)≤ε`; the constant has slack. This branch uses the causal common-event guarantee and preserves probability at least `1−δ`.

The theorem explicitly assumes `0<H`; this matches the positive-horizon convention in the source algorithm and avoids empty-horizon ambiguity.

## Current independent exact-source validation

The independent fresh dependency-order build/probe is running; its hash-pinned manifest is `scripts/finite-horizon-final-theorem-sources.sha256` and its separate output directory is `.local/finite-horizon-final-theorem-fresh-audit/`. Results will be appended once the final exit code and every export probe are checked.

## Independent exact-source compile and axiom audit

The complete staged chain was hash-pinned in `scripts/finite-horizon-final-theorem-sources.sha256` and freshly compiled in dependency order by `scripts/audit-finite-horizon-final-theorem-fresh.sh` into `.local/finite-horizon-final-theorem-fresh-audit/`. All 13 staged-module hashes matched; all 13 modules compiled and the audit exited 0 without Lean errors or warnings. The import probe covered 109 declarations across the chain. Every result was either axiom-free or used only `[propext, Classical.choice, Quot.sound]`; no `sorryAx` occurred. Both `mainSample_causalFinitePolicy` and `exists_universal_causalFinitePolicy_sample_constant` report only those standard axioms. This is an isolated staged-chain verification, not production integration evidence.

## Final statement/output recheck

A second source-only check found no further mismatch in the exact output quantifiers. `exists_universal_causalFinitePolicy_sample_constant` places `c₀` outside all finite carriers and problem parameters, and the sample-count premise is per `(h,s,a)` as in the source. The event uses one fixed `E`, one complete data array, and the same deterministic empirical backward planner throughout. Its all-natural-`h` quantifier contains every source stage; after H, both true and empirical suffixes are empty. At each included `(h,s,a)`, `policyTrajectoryQSuffix` is `DecisionStage.trajectoryQ` for the controlled suffix, so the first action is genuinely forced and only subsequent actions follow the fitted policy.

There is no external estimator argument or measurability hypothesis: this is the concrete deterministic planner. The data type is a finite Pi type over `SampleIndex`; with the local top measurable structure on finite `State`, every data subset is measurable, and all data-dependent selector functions on this finite domain are measurable. Thus the event's probability under the actual product `samplingLaw E N` does not rely on an omitted measurability premise.

For `δ≥1`, the proof does exactly use `0≤(samplingLaw E N).real event` and concludes `1−δ≤probability`; it does not invoke logarithms or the concentration theorem. This branch retains the explicit positive-N input required to construct the empirical rows. The source text's `ε>0` and `ε≤H` also imply H>0, so the formal positive-horizon premise is redundant but consistent. No further source/quantifier mismatch found beyond the already documented positive-N convention and concrete causal tie rule.

Production integration: the three production sources match the independently reviewed staged bodies, with qualified imports. The full project export compiled and audited 2,584 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`. The positive-N and causal-planner scope above remains explicit.
