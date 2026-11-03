# Independent audit: exact Q-comparison source parameters

Reviewed exact staged `.local/QLearningChiSourceParametersDraft.lean`, SHA-256 `f59901a3a4893d67f1df9f064b40c1aecd5c27c9ac7cbaae2903175e93b09e4e`, against its imported residual closure and the source. The builder note `docs/builder-q-learning-chi-source-parameters-draft.md` contains stale earlier hashes/status paragraphs; this review binds only to the exact SHA above. Source review, fresh staged compile, and all-eight-export axiom probes are complete.

## Formula and domain audit

The source `eq:Q-comparison-parameters` at `generative_model_model_free.tex:1087–1089` sets

```text
etaBar = min(1, 2 log(T)^3 / (c2 (1-gamma) T).
```

`qChiSourceRateEnvelope` in the imported residual draft preserves both the cap and `c2` denominator. Under `gamma<1`, `c2>0`, and `T≥2`, the logarithm is positive and the denominator is positive, so the uncapped ratio is positive and its minimum with one remains strictly positive. The actual MDP supplies `0≤gamma<1`; the generic positivity helper needs only the relevant `gamma<1` half.

The source `eq:defn-rho-b-model-free-proof` at lines 1396–1400 sets `rho=8 etaBar log(4SAT/delta)` and `b=2rho/(1-gamma)`. `qChiSourceRadius` and `qChiSourceRewardShift` preserve those formulas exactly. For finite nonempty state/action sets (`S,A≥1`), `T≥2`, and `0<delta<1`, the logarithm argument is strictly greater than one, hence `rho>0`. The source reward shift is positive, and `qChiSourceRewardShift_eq` identifies it exactly with `2*rho*M.effectiveHorizon`; no approximation or extra slack is introduced. No `c1` condition is needed for these deterministic parameter facts; it enters the separate rate schedule/fluctuation bounds.

The two source-substitution helper theorems retain their fixed-point equality and pairwise value span as explicit premises, and derive `rho≥0` from the stated source domains. Their conclusions are precisely the lower residual bounds with `(2-gamma)rho H` slack for the plus and minus orientations. The final `qChi_actualComparatorResidual_source_parameters` corollary discharges both fixed-point and span facts using the actual constructed robust comparators and the previously audited residual/range chain. The existential proof of `rho≥0` is derived evidence, not a new distribution or source assumption.

These declarations consume the source parameter choices only in the deterministic residual lower-bound step. They do not prove the simplified residual upper bound `(2rho+sqrt(rho))H`, the source fluctuation event, confidence union, residual absorption for sample-dependent iterates, part (ii) comparator closeness, or the final Q-learning rate. No source/statement mismatch found for the exact parameter formulas, domains, or residual lower-bound consumption.

## Fresh exact-source compile and axioms

Exact target source compiled with exit 0 and no diagnostics into `.local/q-chi-source-parameters-independent-audit/QLearningChiSourceParametersDraft.olean`. It was compiled against the separately rebuilt exact residual closure `.local/q-chi-residual-independent-audit`, whose top source was SHA `e61a93ba98ba2a83575adcb16dd4c40bc1a7121c2a74a370c53deef4c71c01da`. The exact target compile log is empty at `.local/q-chi-source-parameters-independent-audit/compile.log`.

The fresh `ImportAudit.lean` probes all eight exports: envelope positivity, radius positivity, reward-shift identity, plus and minus generic source substitutions, envelope cap, reward-shift positivity, and actual-comparator source consumption. Every transitive axiom result is limited to `propext`, `Classical.choice`, and `Quot.sound`; output is `.local/q-chi-source-parameters-independent-audit/axioms.log`.

This is staged-source evidence only. Production integration and the stochastic/source theorem closure remain separate.

## Production integration

The reviewed exact source-parameter results are integrated as `Formalization/ModelFree/QLearningChiSourceParameters.lean`. The declaration and proof bodies match the reviewed staged source; imports and status comments were updated where required. The full project check compiled 258 modules and audited 3,407 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
