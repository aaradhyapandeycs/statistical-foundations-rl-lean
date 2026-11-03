# Independent review: discounted trajectory occupancy

**Verdict: PASS for the source's stationary-policy discounted state and state–action occupancy formulas, their normalized finite laws, and deterministic-policy factorization, within the represented trajectory model.** The actual source optimum can be supplied by the separately proved greedy deterministic policy, but this module does not itself import or name that optimal policy. This is a scoped ordinary review, not an author-approved frozen-declaration audit or a whole-chapter certification.

The reviewer did not author `.local/DiscountedOccupancy.lean`. I authored part of its imported `FinitePrefixBridge.lean`; retain its separate independent review in `docs/critic-finite-prefix-bridge.md`. The full-episode occupancy bridge likewise has a separate review in `docs/critic-occupancy-bridge.md`.

## Source-first reconstruction

`source/upstream/tex/chapters/prelim.tex:31–52,63–74` specifies a stationary finite MDP with stochastic kernels, a normalized initial distribution and stationary randomized policy, and `0 ≤ γ < 1`. Lines 145–160 define, for every state and action,

```text
d^π(s;ρ)   = (1−γ) Σ_{t=0}∞ γ^t P(s_t=s | s₀∼ρ),
d^π(s,a;ρ) = (1−γ) Σ_{t=0}∞ γ^t P(s_t=s, a_t=a | s₀∼ρ).
```

The first action is selected at time 0 using π at `s₀`; the next-state draw gives `s₁`. Hence the γ=0 state law is ρ and the joint law is `ρ(s)π(a|s)`. Both discounted laws must be nonnegative and normalized. Stationarity gives the joint/state factorization `d^π(s,a;ρ)=d^π(s;ρ)π(a|s)` without requiring a visited state to have positive mass. Lines 163–176 specialize a deterministic optimal policy to the corresponding action indicator.

## Findings

1. `occupancyStages` and `occupancyIndex` (staged lines 15–22) use `t+1` stages and index t. Thus the prefix includes the action at time t, but `occupancyStateLaw` takes exactly the first t transitions; it starts from the input `ρ`, not from a guessed point state. `occupancyJointAt` uses the actual time-t state-action event from `DecisionStage.stateActionOccupancy`. Both objects use the same stationary model and policy. An independent compiled probe checked state occupancy at `t=0` equals `ρ(s)`, and at `t=1` equals `E_{x∼ρ} E_{a∼π(x)} P(s|x,a)`, confirming both the off-by-one boundary and the action-dependent transition.
2. `finitePrefix_pathState_eq` and `finitePrefix_pathAction_eq` (135–167) identify the finite prefix's indexed state/action with the actual infinite path at t, for every path and every genuine index. The imported `infiniteTrajectoryLaw_map_finitePrefix` identifies the **entire finite-prefix measure** with the independently constructed trajectory law; the imported full-path occupancy bridge supplies the state and joint indicator expectations. `occupancyStateAt_eq_sourceEvent` and `occupancyJointAt_eq_sourceEvent` (209–241) then prove the probabilities of the actual infinite-path events, mixed by the actual finite distribution `ρ`. The mixture `ρ.expectation (fun x ↦ P_x(event))` is the finite total-probability expression for first sampling `s₀∼ρ` and then running the controlled path from that state. The file does not introduce a separately named single joint measure on `(s₀,path)`; its source interpretation uses this exact finite mixture, not an assumed equality or arbitrary default.
3. `discountedStateOccupancy_eq_source` and `discountedJointOccupancy_eq_source` (243–259) identify the exported geometric sums with those actual mixed infinite-path event probabilities, with the factor `1−γ`, exponent t, and matching state/action time. There is no missing terminal term. State terms are nonnegative and bounded by `γ^t`; summability follows from the geometric series. The joint timewise event identity is derived from normalized policy sampling, with no state-support condition.
4. `discountedJointOccupancy_eq` proves the stationary factorization using that timewise identity and the constant policy mass at the queried state. `discountedStateOccupancy_sum` proves total mass one by finite/tsum interchange using the proved geometric domination; `discountedJointOccupancy_sum_action` and `_sum` then prove the correct marginal and joint normalization. Separate nonnegativity proofs support the actual `FiniteDistribution` exports `discountedStateLaw` and `discountedJointLaw`. Neither normalization nor factorization is merely an assumed structure field.
5. `discountedJointOccupancy_deterministic` proves the exact indicator formula for **every** deterministic stationary action function, including ties and zero-support states/actions. It can be instantiated with the actual `optimalGreedyAction` from the separately reviewed `OptimalTrajectoryValue.lean`; this staged file does not import that module or export a specifically named optimal-occupancy theorem. It is therefore accurate to report the general deterministic identity and the available separate optimality construction, while retaining the explicit composition/naming as an integration item.
6. `discountedStateOccupancy_discount_zero` and `discountedJointOccupancy_discount_zero` prove the source boundary `ρ(s)` and `ρ(s)π(a|s)` respectively. The geometric series begins at t=0, where `0^0=1`, and all later terms vanish. No `γ>0` premise or division by an event probability is introduced.

All principal theorem binders expand to the source finite nonempty model, stochastic transition/reward/discount fields, arbitrary stationary randomized π, actual normalized initial distribution ρ, arbitrary t/s/a and, for the deterministic result, an arbitrary deterministic action function. A few helper results take stage lists or indices to prove actual prefix identities; the source-facing conclusions supply the stationary list and valid index themselves. There is no assumed occupancy identity, measure equality, normalization, support positivity, or optimality hypothesis in the final source-formulas.

## Independent verification and identity

An exact staged-source copy with independent appended probes compiled with `bash scripts/lean-local.sh <temporary-file>`. The probes establish the explicit t=0 and t=1 state laws described above and the γ=0 joint boundary. The same run inspected `#print axioms` for `occupancyStateAt_eq_sourceEvent`, `occupancyJointAt_eq_sourceEvent`, `discountedStateOccupancy_eq_source`, `discountedJointOccupancy_eq_source`, `discountedJointOccupancy_eq`, `discountedJointOccupancy_deterministic`, `discountedStateOccupancy_sum`, `discountedJointOccupancy_sum`, `discountedStateOccupancy_discount_zero`, and `discountedJointOccupancy_discount_zero`; all ten used only `propext`, `Classical.choice`, and `Quot.sound`. The temporary probe was removed. This is a staged-source check; a future integrated export and full build still require their own checks.

Reviewed SHA-256 values:

| File | SHA-256 |
| --- | --- |
| `.local/DiscountedOccupancy.lean` | `029a6c51d60dfd7e637ec212394354a7471afcfd1bbf9ddf03b432b9e0bf9606` |
| `Formalization/MDP/OccupancyBridge.lean` | `e7c5519936dc6209640ab82da2aff2991bf71f2ee54f5f29d275ba11cd5a9ab5` |
| `Formalization/MDP/FiniteOccupancy.lean` | `ad542b90fe2daeeaa93696f00fe763c7ca1e428042f769be7fd728c5657ab8d0` |
| `Formalization/MDP/FinitePrefixBridge.lean` | `3ca9d38a8b1014054e83a318476b9fc4316573be5da3624cc20f70ccea87b6d7` |
| `Formalization/MDP/InfiniteTrajectory.lean` | `60c4f2c0279014ba54f6d0165e01d86ba407f2f72f93f4e9c493a6b8b86e33e9` |
| `Formalization/MDP/InfiniteReturn.lean` | `0892b7c828e27835d4ee0f0ba48a5876bc26f05a92790da51f47df09e0730c8c` |
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` |
