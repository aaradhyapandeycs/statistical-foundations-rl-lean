# Independent source review: chi-square residual consumption

Status: source/semantic review only; no compiler invocation in this review. Exact staged source: `QLearningChiResidualDraft.lean` (private staged draft, not shipped), SHA-256 `e61a93ba98ba2a83575adcb16dd4c40bc1a7121c2a74a370c53deef4c71c01da`. The builder handoff is `docs/builder-q-learning-chi-residual.md`. The source currently pinned in the checkout is `source/upstream/tex/chapters/generative_model_model_free.tex`.

## Source formulas and comparison

The source's `eq:Q-comparison-parameters` (lines 1087–1089) defines
`etaBar = min(1, 2 log(T)^3 / (c2 (1-gamma) T))`. The draft's `qChiSourceRateEnvelope` retains the `c2` denominator and the cap at one. The source `eq:defn-rho-b-model-free-proof` (lines 1396–1400) sets `rho=8 etaBar log(4 S A T/delta)` and `b=2 rho/(1-gamma)`; the three draft definitions match these expressions, with reward shift written as `2*rho/(1-gamma)`.

The source residual interval is equation `eq:Q-comparison-residual-lower-upper` (lines 1671–1677):

```text
 gamma sqrt(rho Var_P(V+)) + (2-gamma)rho/(1-gamma)
       <= Qres+ <= (2rho+sqrt(rho))/(1-gamma).
```

The lower inequality is directly matched by the draft's generic plus residual theorem, after substituting `H=1/(1-gamma)`. The draft also proves a sharper intermediate upper expression `2rho H + gamma sqrt(rho Var_P(V+))`; using `Var_P(V+)<=H^2` and `gamma<=1` yields exactly the source's simplified upper bound. The final staged module does not package that last simplification, so consumers must not claim the displayed source upper bound solely from this module.

For the minus residual, the draft derives the estimate separately using the minus robust fixed-point equation and its residual orientation `r + gamma P Vminus - Qminus`. It applies the support comparison to `-Vminus`, explicitly uses variance invariance under negation, expectation negation, and `sSup(-v)=-sInf(v)`. This is the right sign handling: the minus residual's reward shift contributes positive `b`, and no unsupported symmetry assertion is used. The actual-comparator theorem instantiates both actual robust fixed points and consumes the range theorem's two pairwise-span results; it does not leave fixed-point or range conditions as user assumptions.

## Assumptions and scope

The generic helper's pairwise span and fixed-point equation premises are legitimate intermediate assumptions; `qChi_actualComparatorResidual_lower` discharges them from the exact constructed robust fixed points and the independently staged robust range module. This is a deterministic support-comparison argument only. It does not prove etaBar/rho positivity from source parameter domains, a sample-size event, the Freedman fluctuation bound, the union over coordinates/late times, or the sample-dependent iterate absorption. The scalar `gamma/6 <= 2-gamma` is correctly sufficient to absorb the source's additive noise radius `gamma*rho*H/6` into the lower residual slack `(2-gamma)rho H`; the actual event `|xi_t+|<=Qres+` remains separate. Part (ii), comparator closeness to optimal Q, is also outside this module.

No source/statement mismatch found in the definitions, both sign branches, residual constants, or actual fixed-point consumption. Integration must preserve qualified imports and audit the transitive robust-range dependency. This review does not certify the Lean elaboration or axioms; those require the separately assigned compiler audit.

## Fresh isolated dependency rebuild and export audit

The reviewed top-level source remained exactly SHA `e61a93ba98ba2a83575adcb16dd4c40bc1a7121c2a74a370c53deef4c71c01da`. I rebuilt its full staged import closure in dependency order into an isolated local audit directory (not shipped), using the pinned project Lean executable and the already-built project/Mathlib dependency artifacts (no dependency rebuild):

1. `QLearningRobustComparatorDraft` — `f4523b6f7400791447a3969c87be112c90f87c7eb64ba5a0ce9bbfc14ddfaa70`
2. `QLearningRobustContractionDraft` — `91de4ee4c14cb9a9f9d90bea6381bb8aadeadbc8ea348c4e1f39568568b7a574`
3. `QLearningRobustBallCompactDraft` — `f9f725a6e9601e1bd7383d039591fd6a57d4292af53fbfefc0d3e7ad3ac18708`
4. `QLearningRobustAttainmentDraft` — `351714a982da4b21d279a17314c9cb6a5fb00791105fae7464a7fa5a51307d82`
5. `QLearningRobustRangeDraft` — `644cad4fae188e7cae10cd8ddcfe8b8ea6e0dd2447f6a9e4b76579df3196dc7b`
6. `QLearningChiUpperDraft` — `a1a11cbd1debd8e26bd3bcedd0f13339cd0ae8858d7ab3f6823f23e33d7e2280`
7. `QLearningChiLowerDraft` — `7c3c610082d13523ac7f34f89dded65e96ba5e9eeb630ae200d7cea5aa35e4e8`
8. `QLearningChiComparisonDraft` — `d92b11e3aa6ba74249ec3d18f83fb0bf73ff2829fc597f1b8c687ac6ec7620c0`
9. `QLearningChiResidualDraft` — `e61a93ba98ba2a83575adcb16dd4c40bc1a7121c2a74a370c53deef4c71c01da`

Every final module log is empty and each output `.olean` exists. Import audit `ImportAudit.lean` (in an isolated local audit directory, not shipped) uses `#print axioms` on all seven public declarations: the three parameter definitions, both generic sign residual bounds, actual comparator consumption, and scalar slack domination. Each reports only `propext`, `Classical.choice`, and `Quot.sound`. The complete axiom output is `axioms.log` (in an isolated local audit directory, not shipped). This confirms exact staged compilation and transitive axiom closure for the reviewed closure; it does not claim production integration, source-domain parameter positivity, the probability event, or the full source theorem.

## Production integration

The reviewed robust fixed-point residual estimates are now integrated as `Formalization/ModelFree/QLearningChiResidual.lean`; the full stochastic Q-learning rate remains separate. The declaration and proof bodies match the reviewed staged source; imports or status comments were updated where required. The project-wide check compiled 250 modules and audited 3,333 project declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
