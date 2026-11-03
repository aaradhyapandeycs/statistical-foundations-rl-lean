# Independent review: infinite trajectory finite cylinders

**Verdict: PASS for all-length singleton prefix masses under the existing
fixed-initial-state infinite trajectory law.** The separate equivalence to
`DecisionStage.trajectoryLaw` is not proved here.

## Source and reconstructed claim

`prelim.tex` lines 63–73 and 89–102 describes a stationary randomized policy:
from `s₀=s`, sample `a_t` according to `π(·|s_t)` and then `s_{t+1}` according
to `P(·|s_t,a_t)` for every `t ≥ 0`. For an observed history
`h_k=(a_k,s_{k+1})`, `k=0,…,n`, the singleton cylinder must have probability

```text
π(a₀|s₀) P(s₁|s₀,a₀) × ∏_{k=1}^n π(a_k|s_k) P(s_{k+1}|s_k,a_k).
```

There are `n+1` observed pairs. This probability identity does not need
positive probability for any history, a discount factor, or a reward bound.
The whole family of cylinder masses must sum to one.

## Findings

- The existing `InfiniteTrajectory.lean` law stores path coordinate `k` as
  `(a_k,s_{k+1})`; its first-step measure is the correct policy-transition
  product and its `historyKernel` uses the most recently reached state. The
  reviewed `history_singleton_step` result (staged file lines 20–38) obtains
  the joint singleton measure from that actual law's history/next-pair
  composition product. It never divides by a history probability, so includes
  unreachable histories correctly.
- `historyCut` (40–43) drops precisely the last coordinate. The cylinder
  equality (45–68) proves equality of actual events, using index case-splitting
  to cover all coordinates through `n+1`. The successor mass theorem then
  multiplies the prefix mass by `π(a_{n+1}|s_{n+1})P(s_{n+2}|s_{n+1},a_{n+1})`.
  Its `n`-th preceding pair supplies `s_{n+1}`, while the next pair supplies
  the current action and subsequent state: there is no off-by-one mismatch.
- The base case (82–111) is the one-pair cylinder `π(a₀|s₀)P(s₁|s₀,a₀)`.
  `historyMass` (113–130) recursively forms the exact product above in
  `ℝ≥0∞`; each `ofReal` receives a nonnegative product of finite-distribution
  probabilities. The final theorem (132–143) proves that product equals the
  actual infinite-law cylinder mass for every `n : ℕ` and every history.
  There is no implicit extra hypothesis, aside from the original finite-model
  and probability-vector fields and arbitrary stationary policy. Discount and
  reward belong to the MDP structure but are not used to form the product.
- A separate compiled probe summed `historyMass` over every history at an
  arbitrary `n` and obtained exactly one by the actual prefix probability
  measure. Thus the singleton identities are normalized, not just local
  recurrences. `n=0` is a length-one prefix; the empty history is not encoded
  by `Iic n`, although the full law is separately normalized.
- This file does **not** construct a map from arbitrary-length histories to
  `FinitePath` and does **not** prove equality to the project's separately
  defined `DecisionStage.trajectoryLaw`. The all-length cylinder formula is
  the needed substantial ingredient, but that cross-representation bridge and
  its use to identify finite and infinite expected returns remain open here.
  No infinite reward, Q semantics, or optimality result follows from this
  file by itself.

## Checks and identity

A temporary copy of the exact staged source with five `#print axioms` and the
all-histories-sum-to-one probe compiled via
`bash scripts/lean-local.sh <temporary-probe>`. The five
checked results were `infiniteTrajectoryLaw_history_singleton_step`,
`historyCylinder_succ`, `infiniteTrajectoryLaw_prefix_singleton_succ`,
`infiniteTrajectoryLaw_prefix_singleton_zero`, and
`infiniteTrajectoryLaw_prefix_singleton_eq_historyMass`; each used only
`propext`, `Classical.choice`, and `Quot.sound`. The temporary file was
removed. This checks an exact staged source copy, not facade integration.

SHA-256:

- `Formalization/MDP/InfinitePrefix.lean`: `7f84be927abfd081e14595ad7e03aff4e9c5a353d1dcd3fabdc4058581dcf82b`
- `Formalization/MDP/InfiniteTrajectory.lean`: `60c4f2c0279014ba54f6d0165e01d86ba407f2f72f93f4e9c493a6b8b86e33e9`
- `source/upstream/tex/chapters/prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`

## Post-integration source comparison

Compared the integrated `Formalization/MDP/InfinitePrefix.lean` directly with
the reviewed `.local/InfinitePrefix.lean`. The entire diff names the two local
measurable-space instances `infinitePrefixStateMeasurable` and
`infinitePrefixActionMeasurable`; their carriers and bodies remain `⊤`. No
theorem, definition, proof, import, or other text changed. The reviewed source
semantics and scope therefore carry over; compilation of the integrated export
is a separate integration check. Integrated SHA-256:
`c93faa5934f9ea745e44a2e3a175b3519ce3fa827b47ec60e8cf8311bce43c71`.
