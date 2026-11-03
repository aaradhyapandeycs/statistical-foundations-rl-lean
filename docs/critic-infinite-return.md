# Independent source review: infinite discounted return

**Verdict: PASS for the fixed-initial-state trajectory V definition, its
measurability, integrability and geometric bound, and convergence of expected
partial sums on the same infinite path.** This review covers the exact staged
source hash below; integration and further statements remain separate.

## Source reconstruction

`prelim.tex` lines 31–45 defines finite-state/action stationary MDPs with
normalized transition laws, deterministic rewards in `[0,1]`, and discount
`γ ∈ [0,1)`. Lines 66–73 describe a randomized stationary policy. Lines
89–102 define `V^π(s)` as the expected infinite sum of `γ^t r(s_t,a_t)` under
the controlled trajectory starting at `s₀=s`, with policy sampled at each
state and the model transition following each action. The source bounds this
value by `1/(1−γ)` at lines 104–105. At `t=0` the reward is `r(s,a₀)`, and
when `γ=0` the return is precisely this reward; no strictly positive discount
is assumed. The separately stated Q definition at lines 114–123 forces an
initial action and must remain meaningful even when its policy mass is zero.

## Findings

1. The reviewed `InfiniteTrajectory.lean` builds the actual
   Ionescu–Tulcea law on pairs `(a₀,s₁),(a₁,s₂),…` from the model's normalized
   policy/transition product; `s₀` is an explicit fixed state. The reviewed
   `trajectoryState` (`Formalization/MDP/InfiniteReturn.lean` lines 26–29) recovers `s₀`
   from that argument and `s_{n+1}` from coordinate `n`. The reward term
   (31–34) uses this state together with the **current** coordinate's action
   and exponent `t`. It thus samples the correct state-action pair at every
   time; there is no extra reward for the transition after a term.
2. Lines 47–78 prove `0 ≤ γ^t r_t ≤ γ^t`, summability for each path and the
   bound on the total return using the model fields. They apply at `γ=0` and
   every `0 ≤ γ < 1`. A separate compiled probe established the first term is
   `r(s,(path 0).1)` and that, when `γ=0`, the whole return equals that first
   reward. No extra discount, reward, or trajectory assumption appears.
3. The finite carriers have discrete measurable spaces. Lines 80–102 prove
   each trajectory state and reward term measurable and then the infinite
   return measurable as a pointwise limit of measurable partial sums. Lines
   104–112 prove integrability under the actual probability law from the
   uniform geometric bound. This is an ordinary integral of an actual
   summable path reward, not a Bellman fixed point relabeled as a trajectory
   expectation. `trajectoryExpectedValue` (41–45) is the point-state source V
   integral for this explicit law.
4. `partialDiscountedReturn` (114–117) contains exactly times `0,…,n−1`;
   its bounds and measurability are proved in lines 119–133. Lines 135–151
   apply dominated convergence with the integrable constant `1/(1−γ)` and
   pointwise convergence of the actual geometric partial sums. Thus their
   **integrals on the same infinite-path measure** converge to
   `trajectoryExpectedValue`. Lines 153–165 prove the source's value bound.
5. The proof does not identify these infinite-law partial sums with expected
   values under the project's separately constructed `FiniteTrajectory` law
   for an arbitrary prefix length. The previously reviewed infinite-law module
   provides agreement with its Mathlib iterated history-kernel law for all
   lengths and agreement with the project's `trajectoryLaw` at one stage;
   that is not an all-length bridge. Consequently this module alone does not
   identify trajectory V with existing finite-evaluation limits or Bellman
   fixed points. It also does not construct forced-initial-action Q semantics,
   randomized initial-state law, an optimal V/Q function, or a minimax
   experiment. None of those conclusions is claimed by this review.

The mathematical binders are finite state/action carriers and instances, the
original MDP (which includes nonempty carriers, normalized transition rows,
reward bounds and the discount interval), a randomized stationary policy, a
fixed initial state, and where applicable a natural time or path. No target
summability, measurability, convergence, or Bellman equation is an added
assumption. The model's nonempty carriers ensure its finite action/transition
laws and Ionescu–Tulcea probability measure exist.

## Checks and identity

A copy of the reviewed exact source, with boundary and axiom probes appended,
compiled using `bash scripts/lean-local.sh <temporary-probe>`.
The `t=0` and `γ=0` consequences described above compiled. The six checked
exports `discountedRewardTerm_summable`, `infiniteDiscountedReturn_bounds`,
`measurable_infiniteDiscountedReturn`, `integrable_infiniteDiscountedReturn`,
`tendsto_integral_partialDiscountedReturn`, and `trajectoryExpectedValue_bounds`
used only `propext`, `Classical.choice`, and `Quot.sound`. The temporary probe
was removed. This check compiled a staged local source copy; it is not a
facade/export integration build.

SHA-256:

- `Formalization/MDP/InfiniteReturn.lean`: `16eba3e1adc1cc06fb0f23b400356bbebb923d551744c265ca2dc3fc8a310568`
- `Formalization/MDP/InfiniteTrajectory.lean`: `60c4f2c0279014ba54f6d0165e01d86ba407f2f72f93f4e9c493a6b8b86e33e9`
- `source/upstream/tex/chapters/prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`

## Post-integration source comparison

Compared the integrated `Formalization/MDP/InfiniteReturn.lean` directly with
the reviewed `.local/InfiniteReturn.lean`. The entire diff names the two local
measurable-space instances `infiniteReturnStateMeasurable` and
`infiniteReturnActionMeasurable`; their carriers and bodies remain `⊤`. No
theorem, definition, proof, import, or other text changed. The reviewed source
semantics and scope therefore carry over; compilation of the integrated export
is a separate integration check. Integrated SHA-256:
`0892b7c828e27835d4ee0f0ba48a5876bc26f05a92790da51f47df09e0730c8c`.
