# Independent review: optimal-policy discounted occupancy

**Verdict: PASS for the source's deterministic optimal-policy indicator identity in the represented stationary randomized policy class.** The staged module connects the actual discounted infinite-path joint event sum to the same constructed greedy policy's state occupancy and action indicator, with one unchanged initial distribution ρ. This is a scoped review, not an author-approved frozen-declaration audit or a whole-paper certification.

The reviewer did not author `.local/OptimalDiscountedOccupancy.lean`. I previously reviewed its `DiscountedOccupancy` and `OptimalTrajectoryValue` dependencies independently of their builders; retain `docs/critic-discounted-occupancy.md` and `docs/critic-optimal-trajectory-value.md` for their source/semantic and policy-class boundaries.

## Source-first reconstruction

`source/upstream/tex/chapters/prelim.tex:89–102,114–140` defines trajectory V and forced-first-action Q and states that a deterministic optimal policy simultaneously maximizes both. In the discounted subsection the explicitly represented policy is stationary and randomized (lines 63–74). Lines 145–160 define state and joint occupancies as `(1−γ) Σ_t γ^t` times the actual state and state/action trajectory-event probabilities, with initial state drawn from ρ. Lines 163–176 specialize the same initial distribution and deterministic optimal policy to

```text
d*(s;ρ)   = d^{π*}(s;ρ),
d*(s,a;ρ) = d^{π*}(s,a;ρ) = d*(s;ρ) · 1[a = π*(s)].
```

The identity must hold even for unreachable states or actions not selected by the deterministic policy. The source range includes γ=0. The project constructs optimality over all **stationary randomized** policies; no stronger history-dependent or nonstationary policy comparison is claimed by this file. The forced-first-action interpretation gives a Q value even when a policy assigns that action zero probability; it is not an assertion about arbitrary conditional-probability versions on null events.

## Findings

- `optimalGreedyPolicy` is not a fresh or assumed policy in this module. The imported `OptimalTrajectoryValue.lean` defines it as point masses at `optimalGreedyAction`; its previously reviewed theorems prove the same action function simultaneously dominates every represented stationary randomized policy in actual infinite-trajectory V and forced-action Q. The witness is fixed by M before competitor and state/action choices. No optimality hypothesis is added to the staged specialization.
- `optimalGreedy_discountedJointOccupancy_indicator` applies the separately reviewed general deterministic occupancy factorization to **exactly** `M.optimalGreedyAction`. The same M, initial finite distribution ρ and state s occur on both sides; the left is the joint occupancy of `M.optimalGreedyPolicy`, and the right is the state occupancy of that same policy multiplied by `if a = M.optimalGreedyAction s then 1 else 0`. No alternate policy or initial law is hidden in the proof.
- `optimalGreedy_discountedJointOccupancy_source_and_indicator` (staged lines 33–46) combines that indicator with the source joint geometric series. Its summand uses `ρ.expectation` of probabilities under `M.infiniteTrajectoryLaw M.optimalGreedyPolicy x`, namely the finite total-probability mixture after sampling initial state x according to ρ. It uses `trajectoryState x path t` and `(path t).1` at the **same** zero-based time, factor `(1−γ)`, and exponent t. The imported reviewed state-occupancy source theorem gives the matching actual state-event sum for the very same policy and ρ; the staged result does not assume an unrelated `d*` object or claim a separately named joint initial-state/path measure.
- `optimalGreedy_trajectory_optimal_and_occupancy` packages the same occupancy identity with actual trajectory V/Q domination of every represented stationary randomized π at the selected s and a. The policy is the fixed `M.optimalGreedyPolicy` and therefore does not depend on π, s, a or ρ. The imported `exists_stationary_trajectory_optimal` theorem separately makes the global `∃ f, ∀ π s a` quantifier order explicit.
- No state/action positivity, reachable-state premise, tie uniqueness, extra initial distribution, or pre-assumed optimality/occupancy equality appears in any of the staged theorem signatures. For `a ≠ optimalGreedyAction s`, the joint mass is zero irrespective of state occupancy; for `a` equal to it, joint and state occupancies agree. At γ=0, inherited occupancy theorems give state mass `ρ(s)` and joint mass `ρ(s)π*(a|s)`; the source's indicator formula remains valid. An independent probe below checks the case `ρ(s)=0` as well.

## Independent checks and identity

A temporary copy of the exact staged source with appended probes compiled without diagnostics using `bash scripts/lean-local.sh <temporary-file>`. The probes verify: (i) off-greedy action occupancy is zero, (ii) on-greedy joint occupancy equals state occupancy, and (iii) when γ=0 and the initial mass of s is zero, every optimal joint occupancy at s is zero. These checks use the actual staged/integrated exports, and no positivity assumption.

The same run printed axioms for `optimalGreedy_discountedJointOccupancy_indicator`, `optimalGreedy_discountedJointOccupancy_source_and_indicator`, and `optimalGreedy_trajectory_optimal_and_occupancy`; each reported only `propext`, `Classical.choice`, and `Quot.sound`. The temporary probe was removed. This checks the exact staged source and imported compiled artifacts; a future integrated export and full project build require separate checks.

Reviewed SHA-256 values:

| File | SHA-256 |
| --- | --- |
| `.local/OptimalDiscountedOccupancy.lean` | `8843c58af533717e657ddddf54dd1fa9c95169de4de73387df61b10d8a2307d4` |
| `Formalization/MDP/DiscountedOccupancy.lean` | `029a6c51d60dfd7e637ec212394354a7471afcfd1bbf9ddf03b432b9e0bf9606` |
| `Formalization/MDP/OptimalTrajectoryValue.lean` | `d3fbac88b1bec5e29ad93e9432d6a491f72fb3d9ada243f3a954950b47af21d7` |
| `Formalization/MDP/ForcedPrefixBridge.lean` | `f8b1e459e311c7dfc914f13bd70f9129931bf7b6e3d79b7d2b6d69fe2bc50e3a` |
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` |
