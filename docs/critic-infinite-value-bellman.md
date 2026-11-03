# Independent review: first-step infinite trajectory value

**Verdict: PASS for the all-discount pathwise and expected first-step
identities, and for the explicit `γ=0` Bellman and fixed-point specialization.**
The general-discount source Bellman identity remains open.

## Source-first reconstruction

`prelim.tex` lines 63–73, 89–102 defines a fixed-state stationary policy value
as expected discounted rewards on the actual sequence with action drawn from
π and next state drawn from P. Lines 210–223 assert the state Bellman identity
`V(s) = E_{a∼π(s)} r(s,a) + γ E_{t∼Pπ(s)} V(t)` for all source discounts
`0 ≤ γ < 1`. Its first-step derivation must identify the law of the shifted
tail conditional on the sampled next state with the original trajectory law
started there; merely integrating a shifted path under the original measure is
not by itself this identification. At `γ=0`, the continuation vanishes and the
Bellman identity reduces to the policy expectation of the first reward.

## Findings

1. The reviewed actual law stores `(a₀,s₁),(a₁,s₂),…`, with `s₀` supplied
   separately. `trajectoryTail` (staged source lines 22–24) removes exactly the
   first pair. `infiniteDiscountedReturn_first_step` (26–40) expands the
   summable series into `r(s₀,a₀) + γ return(s₁, tail)`. This is a pathwise
   equality for **every** `0 ≤ γ < 1`; the shifted state's use of the first
   pair's second component and the `n+1` shift of actions/states are correct.
   No transition-law or Bellman identity is assumed to prove it.
2. `infiniteTrajectory_initial_reward` (42–63) maps the *actual* initial
   trajectory pair to its policy-transition measure, integrates the finite PMF
   and sums out its normalized next-state distribution. The result is the
   policy-weighted immediate reward, with no state-positivity assumption.
3. `measurable_shiftedReturn` and `integrable_shiftedReturn` (65–87) treat the
   next state as a **random** finite-valued input and the remainder as a
   measurable shift of the original infinite path. The integrability proof is
   under the original infinite law, using the pointwise geometric bound and
   its probability-measure instance. There is no hidden transition, shifted-law
   or integrability premise.
4. `trajectoryExpectedValue_first_step` (89–114) integrates the actual
   pathwise identity after proving both summands integrable, producing the
   source immediate reward plus γ times the expected shifted return **under
   the original joint path measure**. Its statement is true for all model
   discounts, but it is not yet the displayed source Bellman equation: the
   shifted-return integral has not been identified with
   `E_{t∼Pπ(s)} trajectoryExpectedValue π t`.
5. The `γ=0` results (116–145) legitimately specialize the general first-step
   identity and use the actual first-reward law. They prove the trajectory
   value is a fixed point of the project's genuine `valueBellman`, then use
   the separately proved uniqueness characterization to identify it with
   `valueFixedPoint`. Their premise `M.discount=0` is explicit and source
   permitted; it is not part of the source's general-discount theorem. A
   separate compiled probe also gives `trajectoryExpectedValue π s =
   (π s).expectation (M.reward s)` directly at zero discount.
6. There is no proof in this file of the conditional shifted-tail law, a
   general-length equality to the separately constructed finite trajectory
   expectation, the source Bellman equation for arbitrary positive discount,
   or the general identity with the Bellman fixed point. The general first-step
   identity must not be reported as filling that gap. No Q-value identity is
   established here either.

Inputs are the source finite carriers, a model carrying the original normalized
transition laws, bounded rewards and `0 ≤ γ < 1`, any normalized stationary
policy, and an arbitrary initial state/path where applicable. The only
additional premise occurs on explicitly named zero-discount specializations.
No hoped-for Bellman or shifted-law conclusion is passed in as an assumption.

## Checks and identity

A temporary copy of the exact staged source with an independent zero-discount
immediate-reward probe and seven `#print axioms` checks compiled via
`bash scripts/lean-local.sh <temporary-probe>`. Checked
were `infiniteDiscountedReturn_first_step`, `infiniteTrajectory_initial_reward`,
`measurable_shiftedReturn`, `integrable_shiftedReturn`,
`trajectoryExpectedValue_first_step`,
`trajectoryExpectedValue_bellman_of_discount_zero`, and
`trajectoryExpectedValue_eq_valueFixedPoint_of_discount_zero`. Each used only
`propext`, `Classical.choice`, and `Quot.sound`. The temporary file was
removed. This validates the staged source with imported project artifacts, not
a separately built integrated export.

SHA-256:

- `.local/InfiniteValueBellman.lean`: `ce6542a16994f511e7809a4c184d21662759f823f6e41cd70931b32a9c5af270`
- `Formalization/MDP/InfiniteReturn.lean`: `0892b7c828e27835d4ee0f0ba48a5876bc26f05a92790da51f47df09e0730c8c`
- `Formalization/MDP/InfinitePrefix.lean`: `c93faa5934f9ea745e44a2e3a175b3519ce3fa827b47ec60e8cf8311bce43c71`
- `Formalization/MDP/InfiniteTrajectory.lean`: `60c4f2c0279014ba54f6d0165e01d86ba407f2f72f93f4e9c493a6b8b86e33e9`
- `Formalization/MDP/PolicyValueQ.lean`: `3f1c5c812a7b60a8f99aecce5d7ce02cc3bab92c8335186feccf7e8fbc9b6369`
- `source/upstream/tex/chapters/prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`
