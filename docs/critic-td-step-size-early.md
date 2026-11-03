# Independent source review: corrected TD early-weight bound

Reviewed `.local/TDStepSizeEarly.lean`, SHA-256 `5a22bf277da8eba2bf94f10163ab886a7c8582bd94ffe0b807adfbc7a56d3cfa`, against the finite schedule and `lemma:TD-step-size` in `source/upstream/tex/chapters/generative_model_model_free.tex:307–327`, especially the proof at lines 2286–2311. This is an independent source/semantic review only; no compiler was run in this review.

## Verdict

PASS for the corrected early-weight claim as stated. The schedule is restricted to indices `1≤i≤T`, with no condition on `η₀`; the theorem also requires `t≤T`, so it never applies a finite-prefix premise beyond its defined range. It carries `T≥2`, `0≤γ<1`, positive `c₁,c₂`, `c₁c₂≤1/8`, and the additional premise `log(T)^2≤c₁(1−γ)T`. These match the premises actually used by the source proof. The output covers both endpoints `k=0` and `2k=t` without rounding loss.

The schedule's lower bound plus the explicit large-T condition gives, for every actual suffix index `i`,
`η_i(1−γ) ≥ log(T)^2/(2c₁T)`. The schedule also supplies `η_i∈[0,1]` throughout `1≤i≤t`. Applying the independently audited generic finite-product lemma therefore bounds the weight by `exp(−α(t−k))`, with `α=log(T)^2/(2c₁T)`. From `2k≤t`, `t−k≥t/2`; from `t≥T/(c₂logT)` and `c₁c₂≤1/8`, `αt/2≥2logT`. Thus the exponent is at most `−2logT`, yielding `1/T²`. The finite product argument uses the exact integer count `t−k`, so it handles odd and even t uniformly.

The added large-T condition is essential: the source appendix explicitly invokes it to derive the lower bound on `η_i(1−γ)`, and the earlier isolated-lemma counterexample remains applicable when it is omitted. The added `t≤T` is likewise necessary because the schedule only constrains the first T rates. This corrected helper does not silently assert the printed isolated lemma with its deficient assumptions.

## Scope and remaining source obligation

This statement proves only the early-weight branch for the supplied finite schedule and explicit premises. It does not prove the late-weight branch, the full source `lemma:TD-step-size`, or that the main TD theorem's sample-size budget discharges `log(T)^2≤c₁(1−γ)T` for its chosen constants. Those remain separate source obligations. The existing builder handoff reports that the staged file compiled and its exports had standard-only axioms; independent production integration remains unverified here.

An independent fresh-source compile/axiom audit is complete. The hash-pinned script `.local/audit-td-step-size-early-independent.sh` verified the exact weight dependency `45cebbdcb5ff62d586b28932803ae727ec2f1d31bb814346c7e5886e3c19a59f` and early-bound source hash above, rebuilt both into `.local/td-step-size-early-independent-audit`, and probed all 13 exports. Both compilation steps exited successfully without diagnostics; all exports use only `propext`, `Classical.choice`, and `Quot.sound`. The script retains the explicit `hlarge` and `t≤T` premises; the audit does not alter the source statement.

Production integration: the reviewed source body compiles in the project export with qualified imports; the Q-learning causality file has been given the production module name `QLearningCausality`. The full project check audited 2,755 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
